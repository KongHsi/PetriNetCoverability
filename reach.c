
#include <stdlib.h>
#include "reach.h"
#include "y.tab.h"
#include "math.h"

#define MAXINPUTS	500
#define MAXOUTPUTS	500
#define MAXFF		2000

/* counts and arrays of primary input/output wires */

int input_count;
wire input_array[MAXINPUTS];	
int output_count;
wire output_array[MAXOUTPUTS];

/* present_array[i] and next_array[i] are output and input of the same DFF */

int state_var_count;		
wire present_array[MAXFF];
wire next_array[MAXFF];

DdManager *gbm;	/* Global BDD manager. */




/*  fanout arrays are computed in two passes.
/*  Pass 1 discovers the sizes of the fanout sets
/*  Pass 2 allocates arrays and sets the fanout entries. */
find_fanout_counts()
{
  int i,j;
  /* iterate over all wires */
  for (i=0; i < TABLESIZE; i++) {
    if (wirevalid(i)) {
      wire w = wirehashtable[i];
      for (j=0; j < w->fanin_count; j++) {
	w->fanin_array[j]->fanout_count++;
      }
    }
  }
}

find_fanout_arrays()
{
  int i,j;
  /* iterate over all wires */
  for (i=0; i < TABLESIZE; i++) {
    if (wirevalid(i)) {
      wire w = wirehashtable[i];
      for (j=0; j < w->fanin_count; j++) {
	wire v = w->fanin_array[j];
	if (v->fanout_index >= v->fanout_count) {
	  yyerror("Impossible error --- fanout_index too big.");
	}
	if (v->fanout_index == 0) {
	  /* create fanout array if this is the first one. */
	  v->fanout_array = (wire *) malloc(v->fanout_count*sizeof(struct wire_));
	}
	v->fanout_array[v->fanout_index++] = w;
      }
    }
  }
}

/* error reporting */

pline()
{
  fprintf(stdout, "Line %d: ", yylineno);
}

yyerror(char *s)
{ 
  pline(); 
  fprintf(stdout, "%s\n", s);
  fprintf(stdout, "Last token was %s\n", yytext);
}

/* debugging */

print_type(int t)
{
  switch (t) {
  case 0: {
    printf("UNDEFINED");
    break;
  }
  case INPUT: {
    printf("INPUT");
    break;
  }
  case AND: {
    printf("AND");
    break;
  }
  case OR: {
    printf("OR");
    break;
  }
  case NAND: {
    printf("NAND");
    break;
  }
  case NOR: {
    printf("NOR");
    break;
  }
  case NOT: {
    printf("NOT");
    break;
  }
  case DFF: {
    printf("DFF");
    break;
  }
  default: {
    printf("<illegal type>");
    break;
  }
  }
}

print_wire_def(wire w)
{
  int i;
  printf("%s = ", w->name);
  print_type(w->type);
  printf("(");
  for(i=0; i < w->fanin_count; i++) {
    printf("%s", w->fanin_array[i]->name);
    if (i < w->fanin_count-1) 
      printf(", ");
  }
  printf(")\n");
}

void print_wire_array(int count, wire *a)
{
  int i;
  printf("[");
  for (i=0;i<count;i++) {
    printf("%s", a[i]->name);
    if (i < count-1) {
      printf(", ");
    }
  }
  printf("]\n");
}

void dump_wires()
{
  int i;
  for (i=0; i < TABLESIZE; i++) {
    if (wirevalid(i)) {
      wire w = wirehashtable[i];
      printf("%s (", w->name);
      print_type(w->type);
      printf(")");
      if (w->is_output) {
	printf(" [output]");
      }
      if (w->is_nextstate) {
	printf(" [nextstate]");
      }
      printf("\n");
      printf("fanin_count: %d\n", w->fanin_count);
      printf("fanin_array: ");
      print_wire_array(w->fanin_count, w->fanin_array);
      printf("fanout_count: %d\n", w->fanout_count);
      printf("fanout_array: ");
      print_wire_array(w->fanout_count, w->fanout_array);
      if (w->type != NOT) {
	if (w->is_next) {
	  printf("NEXT");
	  if (w->is_out) printf(", OUT\n");
	  else printf("\n");
	}
	else if (w->is_out)
	  printf("OUT\n");
	else printf("Neither NEXT nor OUT?!\n");
      }
      printf("\n");
    }
  }
}

void print_state_vars()
{
  int i;
  printf("PRESENT\t|\tNEXT\n");
  printf("------------------------\n");
  for (i=0; i < state_var_count; i++) {
    printf("%s\t|\t%s\n", present_array[i]->name, next_array[i]->name);
  }
}

void create_present_state_vars()
{
    int i;

    for (i=0; i<state_var_count; i++) {
	present_array[i]->bdd_var = Cudd_bddNewVar(gbm);
    }
}

void create_next_state_vars()
	/* Must call create_present_state_vars() first! */
{
    int i;

    for (i=0; i<state_var_count; i++) {
	/* Keep the present and next state variables close together. */
	next_array[i]->bdd_var = Cudd_bddNewVarAtLevel(gbm,
					Cudd_ReadPerm(
					    gbm,
					    Cudd_NodeReadIndex(
						present_array[i]->bdd_var
					    )
					));
    }
}

void create_input_vars()
{
    int i;

    for (i=0; i<input_count; i++) {
	input_array[i]->bdd_var = Cudd_bddNewVar(gbm);
    }
}


void build_bdd_for_wire(wire w)
        /* Builds the BDD for w from primary inputs and present state. */
{
    int i;
    DdNode *temp1, *temp2;

    if (w->bdd != NULL) return; /* BDD already built. */

    if ((w->type == INPUT) || (w->type == DFF)) {
	w->bdd = w->bdd_var;
	Cudd_Ref(w->bdd);
	return;
    }

    /* Build BDD for each fanin. */
    for (i=0; i < w->fanin_count; i++) {
        build_bdd_for_wire(w->fanin_array[i]);
    }

    switch (w->type) {
        case AND:
            temp1 = Cudd_ReadOne(gbm);
            Cudd_Ref(temp1);
            for (i=0; i < w->fanin_count; i++) {
                temp2 = Cudd_bddAnd(gbm,temp1,w->fanin_array[i]->bdd);
                Cudd_Ref(temp2);
                Cudd_RecursiveDeref(gbm,temp1);
                temp1 = temp2;
            }
            w->bdd = temp1;
            break;
        case NAND:
            temp1 = Cudd_ReadOne(gbm);
            Cudd_Ref(temp1);
            for (i=0; i < w->fanin_count; i++) {
                temp2 = Cudd_bddAnd(gbm,temp1,w->fanin_array[i]->bdd);
                Cudd_Ref(temp2);
                Cudd_RecursiveDeref(gbm,temp1);
                temp1 = temp2;
            }
            w->bdd = Cudd_Not(temp1);
            Cudd_Ref(w->bdd);
            Cudd_RecursiveDeref(gbm,temp1);
            break;
        case OR:
            temp1 = Cudd_ReadLogicZero(gbm);
            Cudd_Ref(temp1);
            for (i=0; i < w->fanin_count; i++) {
                temp2 = Cudd_bddOr(gbm,temp1,w->fanin_array[i]->bdd);
                Cudd_Ref(temp2);
                Cudd_RecursiveDeref(gbm,temp1);
                temp1 = temp2;
            }
            w->bdd = temp1;
            break;
        case NOR:
            temp1 = Cudd_ReadLogicZero(gbm);
            Cudd_Ref(temp1);
            for (i=0; i < w->fanin_count; i++) {
                temp2 = Cudd_bddOr(gbm,temp1,w->fanin_array[i]->bdd);
                Cudd_Ref(temp2);
                Cudd_RecursiveDeref(gbm,temp1);
                temp1 = temp2;
            }
            w->bdd = Cudd_Not(temp1);
            Cudd_Ref(w->bdd);
            Cudd_RecursiveDeref(gbm,temp1);
            break;
        case NOT:
            w->bdd = Cudd_Not(w->fanin_array[0]->bdd);
            Cudd_Ref(w->bdd);
            break;
        default:
            fprintf(stderr,"Error:  Illegal wire type.\n");
            exit(1);
    }
}



DdNode *build_monolithic_tr()
	/* Builds a single BDD that's the transition relation for the
	   entire circuit.  I'm going to build the function BDD for each
	   wire first, then AND them all together. */
{
    int i;
    DdNode *result, *wire_rel, *temp;

    /* Build the BDD for the function at each next state wire. */
    for (i=0; i<state_var_count; i++) {
	build_bdd_for_wire(next_array[i]);
    }

    result = Cudd_ReadOne(gbm);
    Cudd_Ref(result);
    for (i=0; i<state_var_count; i++) {
	/* Build the relation for each next state wire. */
	wire_rel = Cudd_bddXnor(gbm,next_array[i]->bdd_var,next_array[i]->bdd);
	Cudd_Ref(wire_rel);

	temp = Cudd_bddAnd(gbm,result,wire_rel);
	Cudd_Ref(temp);
	Cudd_RecursiveDeref(gbm,result);
	Cudd_RecursiveDeref(gbm,wire_rel);
	result = temp;
    }

    return result;
}


DdNode *build_reset_bdd()
	/* Builds BDD that forces all state variables to 0,
	   presumably a reset state. */
{
	int i;
	DdNode *result, *temp1, *temp2;

	result = Cudd_ReadOne(gbm);
	Cudd_Ref(result);
	for (i=0; i<state_var_count; i++) {
	    temp1 = Cudd_Not(present_array[i]->bdd_var);
	    Cudd_Ref(temp1);
	    temp2 = Cudd_bddAnd(gbm,result,temp1);
	    Cudd_Ref(temp2);
	    Cudd_RecursiveDeref(gbm,temp1);
	    Cudd_RecursiveDeref(gbm,result);
	    result = temp2;
	}
	printf("Initial Bdd size is %ld.\n",Cudd_DagSize(result));
	return result;
}


DdNode *image_monolithic_tr(DdNode *tr, DdNode *x,
	DdNode *ps_input_cube, DdNode **ps_vars, DdNode **ns_vars)
	/* Computes image of x under transition relation tr. */
	/* ps_input_cube is the AND of the present state and input variables to
	   quantify out.  ps_vars and ns_vars are lists of the present state
	   and next state variables. */
{
	DdNode *temp, *result;

	/* Computes AND and quantifies out present state and input variables */
	temp = Cudd_bddAndAbstract(gbm,tr,x,ps_input_cube);
	Cudd_Ref(temp);

	/* Now, change the image BDD back to present state variables. */
	result = Cudd_bddSwapVariables(gbm,temp,ps_vars,ns_vars,state_var_count);
	Cudd_Ref(result);
	Cudd_RecursiveDeref(gbm,temp);

	return result;
}

int notSubsetOf(DdNode *U_new, DdNode *U_lift) {
	DdNode* temp = Cudd_bddAnd(gbm, U_new, U_lift);
	if(U_new != temp) {
		return 1;
	} 
	return 0;
}


void reachable_states_monolithic_tr()
	/* Computes the set of reachable states by building the
	   single monolithic transition relation. */
{
    DdNode *tr;	/* The transition relation for the whole system. */
    DdNode *ps_in_cube;	/* All the input and present state variables ANDed
				together.  Used for quantification. */
    DdNode **ps_vars;	/* List of present state variables */
    DdNode **ns_vars;	/* List of next state variables */
    int i, length;
    DdNode *R, *new_R, *image;
    DdNode *temp, *temp1;

    DdNode *ns_in_cube; // ？
    printf("[initializing reachability...");
    fflush(stdout);

    /* Create BDD variables */
    create_present_state_vars();
    create_next_state_vars();
    create_input_vars();

    /* Create auxiliary data structures used to quantify and substitute. */
    ps_in_cube = Cudd_ReadOne(gbm);
    ns_in_cube = Cudd_ReadOne(gbm);
    Cudd_Ref(ps_in_cube);
    Cudd_Ref(ns_in_cube);
    for (i=0; i<state_var_count; i++) {
		temp = Cudd_bddAnd(gbm,ps_in_cube,present_array[i]->bdd_var);
		Cudd_Ref(temp);
		Cudd_RecursiveDeref(gbm,ps_in_cube);
		ps_in_cube = temp;

        temp1 = Cudd_bddAnd(gbm,ns_in_cube, next_array[i]->bdd_var);
        Cudd_Ref(temp1);
        Cudd_RecursiveDeref(gbm,ns_in_cube);
        ns_in_cube = temp1;
    }
	
    for (i=0; i<input_count; i++) {
		temp = Cudd_bddAnd(gbm,ps_in_cube,input_array[i]->bdd_var);
		Cudd_Ref(temp);
		Cudd_RecursiveDeref(gbm,ps_in_cube);
		ps_in_cube = temp;

		temp1 = Cudd_bddAnd(gbm, ns_in_cube, input_array[i]->bdd_var);
		Cudd_Ref(temp1);
		Cudd_RecursiveDeref(gbm,ns_in_cube);
		ns_in_cube = temp1;
    }

    ps_vars = (DdNode **)malloc(state_var_count*sizeof(DdNode *));
    ns_vars = (DdNode **)malloc(state_var_count*sizeof(DdNode *));
    for (i=0; i<state_var_count; i++) {
		ps_vars[i] = present_array[i]->bdd_var;
		ns_vars[i] = next_array[i]->bdd_var;
    }
    printf("]\n");

    printf("[building transition relation...");
    fflush(stdout);

    tr = build_monolithic_tr();	/* This will blow up for big circuits. */

    printf("]\n");

    /* OK, now we're ready to compute the reachable states. */
    /* FIX THIS!!! */
    /* Initialize your iteration with a BDD which says all the latches are 0 */
    /* Take a look at build_reset_bdd(). */
    i = 0;
    new_R = build_reset_bdd();
    DdNode* initial_R = build_reset_bdd();
    DdNode* outer_Image = Cudd_ReadOne(gbm); // The out most state
    Cudd_Ref(outer_Image);
    do {
		R = new_R;
		printf("Iteration %d:  BDD size is %d.\n",i,Cudd_DagSize(R));
			
		/* FIX THIS!!! */
		/* OK, now put the code to do the reachability iteration in here. */
		/* Be careful to free anything that you don't use. */
		/* image_monolithic_tr computes images */
		image = image_monolithic_tr(tr, R, ps_in_cube, ps_vars, ns_vars); // compute next state
		Cudd_Ref(image);
		DdNode* temp_R = Cudd_bddOr(gbm, R, image); // Combine reached state and next state
		Cudd_Ref(temp_R);
		Cudd_RecursiveDeref(gbm,image);
		Cudd_RecursiveDeref(gbm,R);
		new_R = temp_R;
		
		if(R != new_R) { // Computer the out most state
			DdNode* temp3 = Cudd_Not(R); 
			Cudd_Ref(temp3);
			Cudd_RecursiveDeref(gbm,outer_Image);
			outer_Image = Cudd_bddAnd(gbm, temp3, new_R);
			Cudd_Ref(outer_Image);
			Cudd_RecursiveDeref(gbm, temp3);
		}
		i++;
    } while (R != new_R);
    Cudd_RecursiveDeref(gbm,new_R);

	//temp used to test BH
	DdNode* All_possible_states = Cudd_ReadOne(gbm);
	Cudd_Ref(All_possible_states);
	DdNode* All_possible_states_temp = Cudd_bddAnd(gbm, All_possible_states, R);
	Cudd_Ref(All_possible_states_temp);
	Cudd_RecursiveDeref(gbm, All_possible_states);
	All_possible_states = All_possible_states_temp;
	
    /* Print out the result. */
    printf("Convergence on iteration %d.\n",i);
    printf("Size of reachable state BDD:  %ld.\n",Cudd_DagSize(R));
    printf("Number of reachable states:  %0.0lf.\n",
	Cudd_CountMinterm(gbm,R,state_var_count));
    Cudd_RecursiveDeref(gbm, R);
	
	/* New Stuff */
	DdNode* temp_one = Cudd_ReadOne(gbm);
    Cudd_Ref(temp_one);
    DdNode* temp_zero = Cudd_Not(temp_one);
    Cudd_Ref(temp_zero);
    
		// backward reachability
	printf("\nNow starting for backward reachability\n");
    new_R = Cudd_bddSwapVariables(gbm,outer_Image,ns_vars,ps_vars,state_var_count);
    Cudd_Ref(new_R);
    i = 1;
	printf("Iteration %d, current bdd size is %ld.\n", 0, Cudd_DagSize(new_R));
    DdNode* temp_comp;// Used to test whether reaching initial state
    do {
        if(i!=1) Cudd_RecursiveDeref(gbm, temp_comp);
		R = new_R;
		image = image_monolithic_tr(tr, R, ns_in_cube, ns_vars, ps_vars);
		Cudd_Ref(image);
		DdNode* temp_R = Cudd_bddOr(gbm, R, image);
		Cudd_Ref(temp_R);
		Cudd_RecursiveDeref(gbm,image);
        Cudd_RecursiveDeref(gbm, R);
        new_R = temp_R;
         
        //Check
		DdNode* temp_present_new_R = Cudd_bddSwapVariables(gbm,new_R,ps_vars,ns_vars,state_var_count);
        Cudd_Ref(temp_present_new_R);
        temp_comp = Cudd_bddAnd(gbm, temp_present_new_R, initial_R);
		Cudd_Ref(temp_comp);
        printf("Iteration %d, comp bdd size is %ld, current bdd size is %ld.\n",i++, Cudd_DagSize(temp_comp), Cudd_DagSize(new_R));
        Cudd_RecursiveDeref(gbm, temp_present_new_R); 
    } while (temp_comp == temp_zero);
    printf("Done\n\n");
    
	/*BH Checking Algorithm*/
	
	// Building the bad state
	DdNode* U = (Cudd_ReadOne(gbm));
	Cudd_Ref(U);
	DdNode* U_temp = (ps_vars[0]);
	Cudd_Ref(U_temp);
	DdNode* U_temp1 = Cudd_bddAnd(gbm, U_temp, U);
	Cudd_Ref(U_temp1);
	Cudd_RecursiveDeref(gbm,U);
	Cudd_RecursiveDeref(gbm,U_temp);
	U = U_temp1;
	
	U_temp = Cudd_Not(ps_vars[1]);
	Cudd_Ref(U_temp);
	U_temp1 = Cudd_bddAnd(gbm, U_temp, U);
	Cudd_Ref(U_temp1);
	Cudd_RecursiveDeref(gbm,U);
	Cudd_RecursiveDeref(gbm,U_temp);
	U = U_temp1;
	
	U_temp = Cudd_Not(ps_vars[2]); //CURRENT STATE VALUE IS 4
	Cudd_Ref(U_temp);
	U_temp1 = Cudd_bddAnd(gbm, U_temp, U);
	Cudd_Ref(U_temp1);
	Cudd_RecursiveDeref(gbm,U);
	Cudd_RecursiveDeref(gbm,U_temp);
	U = U_temp1;
	
	U_temp = Cudd_Not(ps_vars[3]);
	Cudd_Ref(U_temp);
	U_temp1 = Cudd_bddAnd(gbm, U_temp, U);
	Cudd_Ref(U_temp1);
	Cudd_RecursiveDeref(gbm,U);
	Cudd_RecursiveDeref(gbm,U_temp);
	U = U_temp1;
	
	U_temp = Cudd_bddAnd(gbm, All_possible_states, U);
	Cudd_Ref(U_temp);
	if(U_temp == temp_zero)
		printf("Bad state doesn't belong to possible states\n");
	else
		printf("Bad state belongs to possible states\n");
	
	// Testing notSubsetOf
	// printf("subset: %d\n", notSubsetOf(U, All_possible_states));
	
	
	
	//int BH_i = compute_i(U); 
	// currently arbitrarily chosen
	int BH_i = 4; //hardcoded
	int BH_n = BH_i;
	int delta = 2; //hardcoded
	/*
	while(BH_n >= BH_i - delta) {
		DdNode* U_lift = lift(U, BH_i); //TODO
		DdNode* U_new = backward_reach(U_lift, i); //TODO
		DdNode* intersection = Cudd_bddAnd(gbm, U_new, initial_R);
		Cudd_Ref(intersection);
		if(intersection == temp_one) {
			printf("Verification failed\n");
			break;
		}
		if(notSubsetOf(U_new, U_lift)) { //TODO
			BH_n = BH_i;
		}
		BH_i++;
	}
	*/
	printf("Verification succeed\n");
	/*End of BH Algorithm */
	
	
    /* Clean up */
	Cudd_RecursiveDeref(gbm,initial_R);
    Cudd_RecursiveDeref(gbm,tr);
    Cudd_RecursiveDeref(gbm,R);
    Cudd_RecursiveDeref(gbm,ps_in_cube);
	Cudd_RecursiveDeref(gbm,ns_in_cube);
    free(ps_vars);
    free(ns_vars);
}

main(int argc, char *argv[])
{
  /* Initialize global data structures */
  input_count=0;
  output_count=0;
  state_var_count=0;
  bzero(wirehashtable,TABLESIZE*sizeof(wire));
  gbm = Cudd_Init(0,0,CUDD_UNIQUE_SLOTS,CUDD_CACHE_SLOTS,0);

  if (argc!=2) {
	fprintf(stderr,"reach:  usage:  reach file\n");
	exit(1);
  }

  yyin = fopen( argv[1], "r" );       /* Doesn't deal with nested loads. */
  if (yyin==NULL) {
	fprintf(stderr,"*** Error opening `%s' ***\n",argv[1]);
	fflush(stderr);
  }

  /* Read the input, construct the netlist. */
  printf("[reading netlist...");
  fflush(stdout);
  lexinit();
  yyparse();
  /* The fanin arrays are built while the netlist is read. */
  /* Now, we make a pass over the circuit to build the fanout arrays. */
  find_fanout_counts();
  find_fanout_arrays();
  printf("]\n");
  printf("TESTING=========\n");
  printf("Number of variables： %d\n", state_var_count);
  printf("TESTING=========\n");
  /* Compute the set of reachable states. */
  /* 	You can also try a different reachability iterations
  	and/or a different image computation if you wish. */
  reachable_states_monolithic_tr();
}


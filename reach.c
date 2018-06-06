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

/* Richard's constants */
/* Remember to change/check these!! */
int var_size_k = 4;
int INITIAL_WEIGHT = 2;
int DELTA = 1;
int badStates[28] = {1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
//int badStates[2] = {2,2};
int initialStates[28] = {1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1};
//int initialStates[2] = {15,0};
DdNode* temp_one;
DdNode* temp_zero;

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

DdNode **intToDdNode(int num){
	if(num < 0 || num >= (int)pow(2.0, (double)var_size_k)) {
		printf("ERROR: INVALID LIFTING VALUE. \n");
	}
	DdNode* temp_one = Cudd_ReadOne(gbm);
    Cudd_Ref(temp_one);
    DdNode* temp_zero = Cudd_Not(temp_one);
    Cudd_Ref(temp_zero);
	
	DdNode **nums = (DdNode **)malloc(var_size_k*sizeof(DdNode *));
	int i = 0;
	if(num == 0) {
		nums[i++] = temp_zero;
	}else if(num == 1){
		nums[i++] = temp_one;
	}else {
		while(num > 0) {
			nums[i++] = (num % 2) == 0 ? temp_zero : temp_one;
			num /= 2;
		}
	}
	
	while(i < var_size_k) {
		nums[i++] = temp_zero;
	}
	
	return nums;
}

DdNode *comparatorLessEqual(DdNode **statesA, DdNode **statesB, int startIndex, int compareWithNumberOrStates) {
	DdNode* gtb = Cudd_ReadLogicZero(gbm);
	Cudd_Ref(gtb);
	int i;
	for(i = 0; i < var_size_k; i++) {
		int a, b;
		if(compareWithNumberOrStates == 0) { //Number
			a = i + startIndex;
			b = i;
		} else { //States
			a = i + startIndex;
			b = i + startIndex;
		}
		DdNode* notB = Cudd_Not(statesB[b]);
		Cudd_Ref(notB);
		DdNode* gt = Cudd_bddAnd(gbm, statesA[a], notB);
		Cudd_RecursiveDeref(gbm, notB);
		Cudd_Ref(gt);
		
		DdNode* eq = Cudd_bddXnor(gbm, statesA[a], statesB[b]);
		Cudd_Ref(eq);
		DdNode* eqNgtb = Cudd_bddAnd(gbm, eq, gtb);
		Cudd_RecursiveDeref(gbm, eq);
		Cudd_Ref(eqNgtb);
		
		DdNode* gtbi = Cudd_bddOr(gbm, eqNgtb, gt);
		Cudd_Ref(gtbi);
		Cudd_RecursiveDeref(gbm, gtb);
		gtb = gtbi;
	}
	
	DdNode* result = Cudd_Not(gtb);
	Cudd_Ref(result);
	Cudd_RecursiveDeref(gbm, gtb);
	return result;
}

DdNode *comparatorNumber(DdNode ** vars, int num) {
	DdNode **nums = intToDdNode(num);
	int i = 0;
	DdNode *result = Cudd_ReadOne(gbm);
	Cudd_Ref(result);
	while(i < state_var_count) {
		DdNode *temp = comparatorLessEqual(vars, nums, i, 0);
		DdNode *temp1 = Cudd_bddAnd(gbm, result, temp);
		Cudd_Ref(temp1);
		Cudd_RecursiveDeref(gbm, result);
		Cudd_RecursiveDeref(gbm, temp);
		result = temp1;
		i += var_size_k;
	}
	return result;
}

DdNode *comparatorState(DdNode ** ps_vars, DdNode ** ns_vars) {
	int i = 0;
	DdNode *result = Cudd_ReadOne(gbm);
	Cudd_Ref(result);
	while(i < state_var_count) {
		DdNode *temp = comparatorLessEqual(ps_vars, ns_vars, i, 1);
		DdNode *temp1 = Cudd_bddAnd(gbm, result, temp);
		Cudd_Ref(temp1);
		Cudd_RecursiveDeref(gbm, result);
		Cudd_RecursiveDeref(gbm, temp);
		result = temp1;
		i += var_size_k;
	}
	return result;
}

DdNode *lift(DdNode* x, int bound, DdNode ** ps_vars, DdNode ** ns_vars, DdNode *ps_in_cube){
	DdNode *weightBound = comparatorNumber(ns_vars, bound);
	DdNode *order = comparatorState(ps_vars, ns_vars);
	DdNode *andAbove = Cudd_bddAnd(gbm, weightBound, order);
	Cudd_Ref(andAbove);
	Cudd_RecursiveDeref(gbm, order);
	Cudd_RecursiveDeref(gbm, weightBound);
	
	DdNode *temp = Cudd_bddAndAbstract(gbm,andAbove,x,ps_in_cube); //WHY PS not NS? also ask image_monolithic_tr.. i think i forgot this again, it quantifies out...
	Cudd_Ref(temp);
	
	DdNode *result = Cudd_bddSwapVariables(gbm,temp,ps_vars,ns_vars,state_var_count);
	Cudd_Ref(result);
	Cudd_RecursiveDeref(gbm,temp);
	return result;
}

DdNode *buildBadStates(int* badStates, DdNode **ps_vars) {
	int numStates = state_var_count / var_size_k;
	DdNode* U = Cudd_ReadOne(gbm);
	Cudd_Ref(U);
	int i;
	for(i = 0; i < numStates; i++) {
		int index = i * var_size_k;
		int num = badStates[i];
		int counter = 0;
		while(num > 0) {
			if(num % 2 == 0){
				DdNode* U_temp = Cudd_Not(ps_vars[index++]);
				Cudd_Ref(U_temp);
				DdNode* U_temp1 = Cudd_bddAnd(gbm, U_temp, U);
				Cudd_Ref(U_temp1);
				Cudd_RecursiveDeref(gbm,U);
				Cudd_RecursiveDeref(gbm,U_temp);
				U = U_temp1;
			} else {
				DdNode* U_temp = ps_vars[index++];
				Cudd_Ref(U_temp);
				DdNode* U_temp1 = Cudd_bddAnd(gbm, U_temp, U);
				Cudd_Ref(U_temp1);
				Cudd_RecursiveDeref(gbm,U);
				Cudd_RecursiveDeref(gbm,U_temp);
				U = U_temp1;
			}
			num /= 2;
			counter++;
		}
		
		while(counter++ < var_size_k) {
				DdNode* U_temp = Cudd_Not(ps_vars[index++]);
				Cudd_Ref(U_temp);
				DdNode* U_temp1 = Cudd_bddAnd(gbm, U_temp, U);
				Cudd_Ref(U_temp1);
				Cudd_RecursiveDeref(gbm,U);
				Cudd_RecursiveDeref(gbm,U_temp);
				U = U_temp1;
		}
	}
	return U;
}

DdNode *backward_reach(DdNode *states, int bound, DdNode *tr, DdNode **ps_vars, DdNode **ns_vars, DdNode *ns_in_cube ) {
	// make state -> ns_vars
	DdNode *new_R = Cudd_bddSwapVariables(gbm,states,ns_vars,ps_vars,state_var_count);
	Cudd_Ref(new_R);
	DdNode *weightBound = comparatorNumber(ns_vars, bound);
	Cudd_RecursiveDeref(gbm, weightBound);
	DdNode *R;
	do {
		R = new_R;
		DdNode *image = image_monolithic_tr(tr, R, ns_in_cube, ns_vars, ps_vars);
		Cudd_Ref(image);
		DdNode* temp_R = Cudd_bddOr(gbm, R, image); // Why did i comment this part out?
		Cudd_Ref(temp_R); // and this line
		Cudd_RecursiveDeref(gbm, R);
		DdNode* temp_R_weight = Cudd_bddAnd(gbm, temp_R, weightBound);
		Cudd_Ref(temp_R_weight);
		Cudd_RecursiveDeref(gbm,image);
		Cudd_RecursiveDeref(gbm, temp_R); //and this line
		new_R = temp_R_weight;
		/*
		//temp
		int arrr[1] = {0};
		int iii;
		for(iii = 0; iii < 16; iii++) {
			arrr[0] = iii;
			DdNode* ppp = buildBadStates(arrr, ns_vars);
			Cudd_Ref(ppp);
			DdNode* U_temppp = Cudd_bddAnd(gbm, ppp, R);
			Cudd_Ref(U_temppp);
			if(U_temppp != temp_zero) {
				printf("%d ", iii);
			}
			Cudd_RecursiveDeref(gbm,ppp);
			Cudd_RecursiveDeref(gbm,U_temppp);
		}
		printf("\n");
		*/
	} while ((new_R != R) && (new_R != Cudd_ReadLogicZero(gbm)));
	Cudd_RecursiveDeref(gbm, new_R);
	new_R = Cudd_bddSwapVariables(gbm,R,ps_vars,ns_vars,state_var_count);
	Cudd_Ref(new_R);
	Cudd_RecursiveDeref(gbm, R);
	return new_R;
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

    DdNode *ns_in_cube; // ?
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
	
	// 1 and 0
	temp_one = Cudd_ReadOne(gbm);
    Cudd_Ref(temp_one);
    temp_zero = Cudd_Not(temp_one);
    Cudd_Ref(temp_zero);
	
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
    //new_R = build_reset_bdd();
	
	new_R = buildBadStates(initialStates, ps_vars);
    DdNode* initial_R = buildBadStates(initialStates, ps_vars);
    /*
	DdNode* outer_Image = Cudd_ReadOne(gbm); // The out most state
    Cudd_Ref(outer_Image);
    do {
		R = new_R;
		printf("Iteration %d:  BDD size is %d.\n",i,Cudd_DagSize(R));
			
		// FIX THIS!!! 
		// OK, now put the code to do the reachability iteration in here. 
		// Be careful to free anything that you don't use. 
		// image_monolithic_tr computes images 
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
		
		//temp
		//int arrr[1] = {0};
		//int iii;
		//for(iii = 0; iii < 16; iii++) {
		//	arrr[0] = iii;
		//	DdNode* ppp = buildBadStates(arrr, ps_vars);
		//	Cudd_Ref(ppp);
		//	DdNode* U_temppp = Cudd_bddAnd(gbm, ppp, R);
		//	Cudd_Ref(U_temppp);
		//	if(U_temppp != temp_zero) {
		//		printf("%d ", iii);
		//	}
		//	Cudd_RecursiveDeref(gbm,ppp);
		//	Cudd_RecursiveDeref(gbm,U_temppp);
		//}
		//printf("\n");
		
		i++;
    } while((new_R != R) && (new_R != Cudd_ReadLogicZero(gbm)));
    Cudd_RecursiveDeref(gbm,new_R);

	//temp used to test BH
	DdNode* All_possible_states = Cudd_ReadOne(gbm);
	Cudd_Ref(All_possible_states);
	DdNode* All_possible_states_temp = Cudd_bddAnd(gbm, All_possible_states, R);
	Cudd_Ref(All_possible_states_temp);
	Cudd_RecursiveDeref(gbm, All_possible_states);
	All_possible_states = All_possible_states_temp;
	
    // Print out the result.
    printf("Convergence on iteration %d.\n",i);
    printf("Size of reachable state BDD:  %ld.\n",Cudd_DagSize(R));
    printf("Number of reachable states:  %0.0lf.\n",
	Cudd_CountMinterm(gbm,R,state_var_count));
    Cudd_RecursiveDeref(gbm, R);
	
    
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
		
		//temp
		//int arrr[1] = {0};
		//int iii;
		//for(iii = 0; iii < 16; iii++) {
		//	arrr[0] = iii;
		//	DdNode* ppp = buildBadStates(arrr, ns_vars);
		//	Cudd_Ref(ppp);
		//	DdNode* U_temppp = Cudd_bddAnd(gbm, ppp, R);
		//	Cudd_Ref(U_temppp);
		//	if(U_temppp != temp_zero) {
		//		printf("%d ", iii);
		//	}
		//	Cudd_RecursiveDeref(gbm,ppp);
		//	Cudd_RecursiveDeref(gbm,U_temppp);
		//}
		//printf("\n");
		
    } while ((new_R != R) && (new_R != Cudd_ReadLogicZero(gbm)));
    printf("Done\n\n");
	*/
	
	/*BH Checking Algorithm*/
	
	// Building the bad state
	DdNode* U = buildBadStates(badStates, ps_vars);
	/*
	int asdasd[1] = {0};
	if(initial_R != buildBadStates(asdasd, ps_vars))
		printf("ahha");
	*/
	
	/*
	DdNode* U_temp = Cudd_bddAnd(gbm, All_possible_states, U);
	Cudd_Ref(U_temp);
	if(U_temp == temp_zero)
		printf("Bad state doesn't belong to possible states\n");
	else
		printf("Bad state belongs to possible states\n");
	*/
	
	/*
	// Testing notSubsetOf
	// printf("subset: %d\n", notSubsetOf(U, All_possible_states));
	*/
	
	/*
	//Testing comparator
	DdNode* comparator_test = comparatorNumber(ps_vars, 4);
	DdNode* temppppp = Cudd_bddAnd(gbm, comparator_test, U);
	Cudd_Ref(temppppp);
	comparator_test = temppppp;
	if(comparator_test == temp_zero)
		printf("Bigger\n");
	else {
		printf("Smaller or equal\n");
		printf("%d\n",Cudd_DagSize(comparator_test));
	}
	*/
	
	/*
	printf("Lift before: %d\n",Cudd_DagSize(U));
	DdNode *liftTest = lift(U, 7, ps_vars, ns_vars, ps_in_cube);
	printf("Lift after: %d\n",Cudd_DagSize(liftTest));
	*/
	
	/*
	printf("br before: %d\n",Cudd_DagSize(U));
	DdNode *brTest = backward_reach(U, 2, tr, ps_vars, ns_vars, ns_in_cube);
	printf("br: %d\n",Cudd_DagSize(brTest));
	*/
	
	//int BH_i = compute_i(U); // currently arbitrarily chosen
	int BH_i = INITIAL_WEIGHT; //hardcoded
	int BH_n = BH_i;
	int delta = DELTA; //hardcoded
	
	int flag = 0;
	DdNode* U_lift;
	DdNode* U_new = U;
	
	/*
	printf("br: %d\n",Cudd_DagSize(U_new));
	int a1 = 0, a2=0, a3=0;
	int asdasd[3];
	for(a1=0; a1 < 4;a1++){
		for(a2=0; a2 < 4;a2++){
			for(a3=0; a3 < 4;a3++){
				asdasd[0] = a1;
				asdasd[1] = a2;
				asdasd[2] = a3;
				if(Cudd_bddAnd(gbm, U_new, buildBadStates(asdasd, ps_vars)) != temp_zero)
					printf("%d %d %d\n", a1, a2, a3);
			}	
		}
	}
	*/
		
	while(BH_n >= BH_i - delta) {
		
		U_lift = lift(U_new, BH_i, ps_vars, ns_vars, ps_in_cube);
		/*
		printf("=================================\n");
		for(a1=0; a1 < 4;a1++){
			for(a2=0; a2 < 4;a2++){
				for(a3=0; a3 < 4;a3++){
					asdasd[0] = a1;
					asdasd[1] = a2;
					asdasd[2] = a3;
					if(Cudd_bddAnd(gbm, U_lift, buildBadStates(asdasd, ps_vars)) != temp_zero)
						printf("%d %d %d\n", a1, a2, a3);
				}	
			}
		}
		*/
		
		U_new = backward_reach(U_lift, BH_i, tr, ps_vars, ns_vars, ns_in_cube);
		printf("br: %d\n",Cudd_DagSize(U_new));
		/*
		printf("=================================\n");
		for(a1=0; a1 < 4;a1++){
			for(a2=0; a2 < 4;a2++){
				for(a3=0; a3 < 4;a3++){
					asdasd[0] = a1;
					asdasd[1] = a2;
					asdasd[2] = a3;
					if(Cudd_bddAnd(gbm, U_new, buildBadStates(asdasd, ps_vars)) != temp_zero)
						printf("%d %d %d\n", a1, a2, a3);
				}	
			}
		}
		printf("br: %d\n",Cudd_DagSize(U_new));
		*/
		
		DdNode* intersection = Cudd_bddAnd(gbm, U_new, initial_R); //TODO: probably shouldn't and with initial_r
		Cudd_Ref(intersection);
		if(intersection != temp_zero) {
			printf("Verification failed\n");
			flag = 1;
			break;
		}
		if(notSubsetOf(U_new, U_lift)) {
			BH_n = BH_i;
		}
		BH_i++;
	}
	
	if(flag == 0)
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
  printf("Input count: %d\n", input_count);
  printf("TESTING=========\n");
  /* Compute the set of reachable states. */
  /* 	You can also try a different reachability iterations
  	and/or a different image computation if you wish. */
  reachable_states_monolithic_tr();
}
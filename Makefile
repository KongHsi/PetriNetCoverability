#ARCH = `uname -p`
ARCH = $$CS_MACH

CC = gcc

#CFLAGS = -g -I/isd/users/software/cudd-3.0.0/include
CFLAGS = -g -I/isd/users/software/cudd-3.0.0/cudd

# Use these for department Linux machines...
LFLAGS = -L/isd/users/software/cudd-3.0.0/cudd/.libs -lcudd -ly -lfl -lm

OBJS = reach.o wirehash.o lex.yy.o y.tab.o

PROGRAM = reach

$(PROGRAM): $(OBJS)
	$(CC) $(CFLAGS) $(OBJS) $(LIBDIR) $(LFLAGS) -o $(PROGRAM)

reach.o:	reach.h y.tab.h reach.c

wirehash.o:	wirehash.c reach.h

y.tab.o: y.tab.c y.tab.h reach.h
y.tab.h y.tab.c: iscas89.y reach.h
	yacc -vd iscas89.y

lex.yy.o: y.tab.h lex.yy.c reach.h
lex.yy.c: iscas89.l
	lex iscas89.l

clean:
	/bin/rm -f $(OBJS) y.output y.acts yacc.tmp yacc.acts lex.yy.c y.tab.c y.tab.h

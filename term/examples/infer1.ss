int foo (int x)
	requires x>=5
	variance [x-5]
	ensures true;
{
	if (x==5)
		return x;
	else 
		return foo(x-1);
}

/*
Lattice for termination

     May-Term
        /\
       /  \
      /    \
     /      \
Non-Term   Term
     \      /
      \    /
       \  /
        \/
				Bot (Unreachable)


1. Precondition: x>=5
	a. Reachable states from the precondition
		x>=5 & x=5: SAT
		x>=5 & x!=5: SAT
	b. NEXT reachable states from the above reachable states
	   (Program state transition)
		(x>=5 & x=5): no loop -> termination (base case)

		(x>=5 & x!=5) & x'=x-1 |- x'>=5 & x'=5: MAY (1)
		(x>=5 & x!=5) & x'=x-1 |- x'>=5 & x'!=5: MAY (2)

		Coverage checking:
		(x>=5 & x!=5) & x'=x-1 |- (x'>=5 & x'=5) | (x'>=5 & x'!=5): VALID (3)

		(1, 2, 3) imply that from the reachable state (x>=5 & x!=5), 
		the program will move to either the state (x'>=5 & x'!=5) (loop)
		or the state (x'>=5 & x'=5) (base case) and nothing else.

		Finding the conditions in which (1) or (2) is reachable
		by refining MAY to VALID (strengthening LHS by (LHS union RHS))

		(1): (x>=5 & x!=5 & x'=x-1) & (x'>=5 & x'=5) <-> x=6 (1-1)
		(2): (x>=5 & x!=5 & x'=x-1) & (x'>=5 & x'!=5) <-> x>6 (2-1)

		(1-1) is the boundary condition for the program transition
		from loop to base case.

		(2-1) is the condition for loop. It will help to infer the variance
		for the loop (in case the variance is not given or is not valid).

		The termination of the loop with program state (x>=5 & x!=5) can be
		proved by the given variance.
	c. Calculating overall termination with the precondition:
		Term (x=5) |_| Term (x!=5) = Term

2. Complement of the precondition: x<5
  a. Reachable states
		x<5 & x=5: UNSAT -> Unreachable
		x<5 & x!=5: SAT
	b. NEXT reachable states from the above reachable states
		(x<5 & x!=5) & x'=x-1 |- x'<5 & x'!=5: VALID (4)

		(4) implies that the program state (x<5 & x!=5) loops infinitely
		by itself (Here we do not need a coverage checking). As a result,
		the program is not terminating under the condition (x<5 & x!=5).
	c. Calculating overall termination
		Unreachable (x=5) |_| Non-Term (x<5 & x!=5) = Non-Term

3. Termination for all input:
		Term (x>=5) |_| Non-Term (x<5) = May-Term
*/

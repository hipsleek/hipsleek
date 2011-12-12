int foo (int x)
	requires true
	ensures true;
{
	if (x==5)
		return x;
	else 
		return foo(x-1);
}

/*
The precondition does not provide any information.
	a. Reachable states from the precondition
		true & x=5: SAT
		true & x!=5: SAT
	b. Program state transition
		x=5: no loop -> termination (base case)
		
		x!=5 & x'=x-1 |- x'=5: MAY (1)
		x!=5 & x'=x-1 |- x'!=5: MAY (2)

		Coverage checking:
		(x!=5) & x'=x-1 |- x'=5 | x'!=5: VALID (3)

	c. The termination of loop by (2) needs to be proved
		by a valid variance. If not, it will be considered
		as May-Term. In this case, the overall termination
		will be:
			Term (x=5) |_| May-Term (x!=5) = May-Term

	d. The May-Term result under the condition x!=5 can be 
		refined by finding the condition that makes (1) become
		VALID. That is
			x!=5 & x'=x-1 & x'=5: SAT <=> x=6
			x!=5 & x'=x-1 & x'=6: SAT <=> x=7
			...

		By fixpoint calculation (?), we have the condition x>5 
		for termination.

		The inferred termination specification:
		case {
			x>5 -> __Term
			x=5 -> __Term      <=> __May-Term
			x<5 -> __Non-Term
		}
		
*/

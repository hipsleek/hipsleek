int foo (int x)

 case {
  x<5 -> variance (-1) ensures false;
  x=5 -> variance (0) ensures res=5;
  x>5 -> case {
    exists(a:x=2*a)
      -> variance (2) ensures false;
    !(exists(b:x=2*b))   
      -> variance (1) [x]
         ensures res=5; }
  }

/*
 case {
  x<5 -> variance (-1) ensures false;
  x=5 -> variance (0) ensures res=5;
  x>5 -> case {
    exists(a:x=2*a)
      -> variance ensures false;
    !(exists(b:x=2*b))   
      -> variance [x]
         ensures res=5; }
	}
*/
/*
requires x>=5
variance
ensures res=5;
*/
{
	if (x==5)
		return x;
	else 
		return foo(x-2);
}

/*
int foo (int x)
	requires true
	ensures true;
{
	if (x==5)
		return x;
	else 
		return foo(x-2);
}
*/
/*

Specification refinement for termination:

case {
	x < 5 -> __NonTerm;
	x = 5 -> __Term; /* base case */
	x > 5 -> __MayTerm
}

Step 1: Calculate reachable states under the precondition:
	x=5
	x!=5

Step 2: Calculate next reachable states with the above reachable
states as seeds
	a. x=5: no loop -> terminating (base case)
	b. x!=5: 
		x!=5 & x'=x-2 |- x'=5: MAY
		x!=5 & x'=x-2 |- x'!=5: MAY

		Coverage checking: VALID

Step 3: Refine MAY results to find termination or non-termination
conditions
		Find termination condition (the condition under which the base 
		case is reachable) 
  		x!=5 & x'=x-2 |- x'=5: MAY	
		
		FixCalc can find the condition x>5. This means the x<5 is the
		non-termination condition (? - Need to be proven). Intuitively,
		the state with the condition x<5 can not reach the base case 
		x=5, so that it is non-terminating. This result can be confirmed
		by the entailment
			x!=5 & x<5 & x'=x-2 |- x'<5: VALID
		
		However, because FixCalc returns an over-approximate result, the
		condition x>5 need to be refined.

			x!=5 & x>5 & x'=x-2 |- x'>5: MAY
			x!=5 & x>5 & x'=x-2 |- x'=5: MAY
			x!=5 & x>5 & x'=x-2 |- x'<5: MAY

		The above implications imply that x>5 -> __MayTerm, based on
		two already-known results:
			x=5 -> __Term
			x<5 -> __NonTerm

	  The __MayTerm result for x>5 can be furthur refined if we 
		change the abstract domain of FixCalc, i.e., {Even, Odd}.
		In this case, by finding the conditions in which x=5 and 
		x<5 are reachable from x>5, we can obtain a better specification

case {
	x < 5 -> __NonTerm;
	x = 5 -> __Term; /* base case */
	x > 5 -> case {
		even(x) -> __NonTerm
		odd(x) -> __Term
	}
}

The refinement of the __MayTerm result need the power of
fixpoint calculator (i.e., adjusting abstract domain automatically?)

*/


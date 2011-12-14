int foo (int x)
	requires true
	ensures true;
{
	if (x==5)
		return x;
	else 
		return foo(x-2);
}

/*
Specification refinement for termination:

case {
	x < 5 -> __NonTerm;
	x = 5 -> __Term; /* base case */
	x > 5 -> __MayTerm
}

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


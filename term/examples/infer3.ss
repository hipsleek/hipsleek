int foo (int x)
	requires x>=5
	variance [x-5]
	ensures true;
{
	if (x==5)
		return x;
	else 
		return foo(x-2);
}

/*
Invalid given variance - Need to be refined

1. Precondition: x>=5
	a. Reachable state: 
		x>=5 & x=5: SAT
		x>=5 & x!=5: SAT
	b. NEXT reachable state:
		(x>=5 & x=5): no loop -> termination (base case)

		(x>=5 & x!=5) & x'=x-2 |- x'>=5 & x'=5: MAY (1)
		(x>=5 & x!=5) & x'=x-2 |- x'>=5 & x'!=5: MAY (2)

		Coverage checking:
		(x>=5 & x!=5) & x'=x-2 |- (x'>=5 & x'=5) | (x'>=5 & x'!=5): MAY (3)

		Finding the remaining next reachable state (weakening the RHS 
		or strengthening the LHS to make (3) valid):
			LHS_1 = LHS & RHS
						= x>=5 & x!=5 & x'=x-2 & x'>=5
						= x>=7

			LHS_2 = LHS \ LHS_1 = x=6 ->* x'<5

			LHS \ RHS = ... (?) = x'<5

2. Proving termination under the condition x<5 (= complement of the given precondition)
		(Same as infer1.ss)
*/


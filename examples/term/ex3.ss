//Example from Dual Analysis for Proving Safety and Finding Bugs

int foo (int x)

{
	if (x = 10)
		return 1;
	else
		return 2 + foo (x + 1); 
}

/*
We have 3 states that need to be considered:
x = 10 -> __Bot
x != 10 -> x <= 9 or x >= 11

Checking terminating property for the
program state x >= 11
loop:
	checkentail x >= 11 |- x+1 >= 11.
	Valid.
reaching other states or base case:
	checkentail x >= 11 |- x+1 <= 9.
	Must_bug.

	checkentail x >= 11 |- x+1 = 10.
	Must_bug.
==> Must_Nonterm

Checking terminating property for the
program state x <= 9
loop:
	checkentail x <= 9 |- x+1 <= 9.
	May_bug.
reaching other states or base case:
	checkentail x <= 9 |- x+1 >= 11.
	Must_bug.

	checkentail x <= 9 |- x+1 = 10.
	May_bug.
==> Must_Term
	checkentail x <= 9 |- x+1 <= 9 | x+1=10.
	Valid.

Overall: May_Term for x != 10.
*/
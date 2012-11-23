int foo (int x)

case {
	x <= 0 -> __Bot
	x > 0 ->
		case {
			x > 5 -> __Must_Nonterm
			x <= 5 -> __Must_Term
		}
}

case {
	x <= 0 -> __Bot
	x > 0 -> __May_Term
}


{
	if (x > 0) {
		if (x > 5) return foo (x + 1);
		else return foo (x - 1);
	} else return 0;
}

/*
There are three abstract states in the above example:
x <= 0 -> __Bot
x > 0 & x > 5
x > 0 & x <= 5

Starting from a state, the program will terminate if
it eventually reach the state of base case. We need
to consider at the boundary when the program state
changes from recursive state to base case's state.

Checking for the state x > 0 & x > 5
loop:
	checkentail x > 0 & x > 5 |- x+1 > 0 & x+1 > 5.
	Valid.
changing to other states:
	checkentail x > 0 & x > 5 |- x+1 > 0 & x+1 <= 5.
	Must_bug.
base case reaching:
	checkentail x > 0 & x > 5 |- x+1 <= 0.
	Must_bug.
==> Must_Nonterm

Checking for the state x > 0 & x <= 5
loop:
	checkentail x > 0 & x <= 5 |- x-1 > 0 & x-1 <= 5.
	May_bug.
changing to other states:
	checkentail x > 0 & x <= 5 |- x-1 > 0 & x-1 > 5.
	Must_bug.
base case reaching:
	checkentail x > 0 & x <= 5 |- x-1 <= 0.
	May_bug.
==> Must_term
*/


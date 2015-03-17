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

============================================
Constraint-based approach
============================================
int foo (int x)
case {
	x = 10 -> __Bot
	x != 10 -> T
}
{
	if (x = 10)
		return 1;
	else
		return 2 + foo (x + 1); 
}

T(!=10) = x != 10 &
          case {x+1 = 10 -> __Bot;
				x+1 != 10 -> T}

T(!=10) = case {x = 9 -> __Bot;
				x != 10 & x != 9 -> T(x!=11 & x!=10)}

T(=9) = __Bot
T(x!=10 & x!=9) = T(x!=11 & x!=10)
                = T(x!=9 & x!=10  & x!=11) or T(x=9)

----------------------------------------------
int foo (int x)
case {
	x = 10 -> __Bot
	x <= 9 -> T1
	x >= 11 -> T2
}
{
	if (x = 10)
		return 1;
	else if (x <= 9)
		return 2 + foo (x + 1); //T1
	else
		return 2 + foo (x + 1); //T2
}

T1 = x <= 9 &
     case {
		x+1 = 10 -> __Bot;
		x+1 <= 9 -> T1;
		x+1 >= 11 -> T2;}
   = case {
		x = 9 -> __Bot;
		x <= 8 -> T1}

T1(x=9) = __Bot
T1(x<=8) = T1(x<=9) = T1(x<=8) or T1(x=9)
(checkentail x<=8 |- x+1=9 --> may_bug)

T2 = x >= 11 &
     case {
		x+1 = 10 -> __Bot;
		x+1 <= 9 -> T1;
		x+1 >= 11 -> T2;}
   = x >= 11 -> T2

T2(x>=11) = T2(x>=12) = T2(x>=11)
(checkentail x>=12 |- x>=11 --> Valid)  

*/


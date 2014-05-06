/**************************************
Example from Gulwani et al. PLDI'08
Program analysis as constraint solving
(Used in CAV'08 - Proving Conditional Termination)
**************************************/

void f (ref int x, int y, int n)
/*
	With the new specification for loop,
	the termination checker can detect that
	f is not terminating if 
		x+y<200 & y<=0
	(y'=y & n'=n & 200<n & y<9 & x'=0 & x'<n' & (y'+x')<200 & y'<=0)
	The function terminates if y>0
*/

//requires n>200 & y<9 & Term[] //ERR
//requires n>200 & y<9 & MayLoop //OK
requires n>200 & y<9 & y>0 & Term[] //OK
ensures x'>=200;
{
	x = 0;
	loop(x, y, n);
}

void loop (ref int x, int y, int n)
/*
  Without the condition n>200, it returns
  (ERR) Term[-x] -> Loop
*/
requires n>200
case {
	x>=n -> requires Loop ensures false;
	x<n -> case {
		x+y>=200 -> requires Term[] ensures x'>=200;
		x+y<200 -> case {
			y<=0 -> requires Loop ensures false;
			y>0 -> requires Term[-x] ensures x'>=200;
		}
	}
}

{
	if (x<n) {
		x = x + y;
		if (x>=200) return;
	}
	loop(x, y, n);
}

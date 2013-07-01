/********************************************************
Example from "Variance Analyses from Invariance Analyses"
Josh Berdine et al. (POPL'07)
*********************************************************/

bool rand_bool () 
requires Term
ensures true;

int rand_int ()
requires Term
ensures true;

//Need fairness assumption for termination

void loop_1 (int x, int y, int a, int b)
requires MayLoop
ensures true;
{
	bool r = rand_bool();
	if (r) {
		loop_2(x, y, a, b);
		loop_1(x, y, a, b);
	}
}

void loop_2 (ref int x, ref int y, int a, int b)
case {
	!(x>a & y>b) -> requires Term ensures x'=x & y'=y;
	(x>a & y>b) -> requires Term[x-a, y-b] ensures (x'<=a | y'<=b);
	//Term[(x-a)+(y-b)]
}
{
	if (x>a && y>b) {
		bool r = rand_bool();
		if (r) {
			loop_3(x);
		} 
		else {
			y = y-1;
		}
		loop_2(x, y, a, b);
	}
}

void loop_3 (ref int x)
case {
	x<=11 -> requires Term ensures x'=x-1;
	x>11 -> requires Term[x] ensures x'=10;
}
{
	x = x-1;
	if (x>10)
		loop_3(x);
}

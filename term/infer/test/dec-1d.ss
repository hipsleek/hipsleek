void loop (int x)
/*
// EXPECTED SPEC
case {
	x=0 -> requires Term ensures true;
	x!=0 -> case {
		x<0 -> requires Loop ensures false;
		x>=0 -> case {
			exists(a: x=2*a) -> requires Term[x] ensures true;
			exists(b: x=2*b+1) -> requires Loop ensures false;
		}
	}
}
*/

requires true
ensures true;

{
	if (x==0) return;
	else loop(x-2);
}

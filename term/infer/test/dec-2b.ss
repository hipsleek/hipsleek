void loop (int x, int y)
/*
// EXPECTED SPEC
case {
	x<=0 -> requires Term ensures true;
	x>0 -> case {
		y<0 -> requires Term[x] ensures true;
		y>=0 -> requires Term[y] ensures true;
	}
}
*/

requires true
ensures true;

{
	if (x<=0) return;
	else loop(x+y, y-1);
}

// The sequence of x is not neither decreasing nor increasing
// The program should stop within 1-step execution
void loop (int x) 
/*
//EXPECTED SPEC
case {
	x<=0 -> requires Term ensures true;
	x>0 -> requires Term ensures true;
}
*/

requires true
ensures true;

{
	if (x<=0) return;
	else loop(1-x);
}

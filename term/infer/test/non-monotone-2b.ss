// The sequence of x is not neither decreasing nor increasing
// The program should stop within 1-step execution
void loop (int x) 

requires true
ensures true;

{
	if (x<=0) return;
	else loop(10-2*x);
}

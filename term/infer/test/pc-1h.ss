void loop (int x, int y) 
requires true
ensures true;
{
	if (x<=0) return;
	else loop(x+y, -2-y);
}

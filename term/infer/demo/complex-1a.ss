void loop(int x, int y)
requires true
ensures true;
{
	if (x<y) return;
	else if (x>y)
		loop(x-1,y);
	else
		loop(2*x+1,y+1);
}

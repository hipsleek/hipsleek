void loop (int x) 
requires true
ensures true;
{
	if (x>5 || x<1) return;
	else loop(x-1);
}

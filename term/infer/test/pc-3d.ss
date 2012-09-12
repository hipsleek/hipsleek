
void loop (int x, int y, int z)
requires true
ensures true;
{
	if (x<=0) return;
	else loop(x+y, y+z, 3-z);
}

/*
void loop (int x, int y)
requires true
ensures true;
{
	if (x<=0) return;
	else loop(x+y, -y);
}
*/
/*
void loop (int x, int y)
requires true
ensures true;
{
	if (x<=0) return;
	else loop(x+y, -1-y);
}
*/

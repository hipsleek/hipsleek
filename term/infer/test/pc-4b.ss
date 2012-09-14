void loop (int x, int y, int z)

requires true
ensures true;

{
	if (x<=0) return;
	else loop (x+y, z-y, z);
}

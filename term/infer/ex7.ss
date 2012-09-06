void loop (int x)
requires true
ensures true;
{
	if (x == 0) return;
	else if (x == 1) return;
	else loop(x-2);
}

void main ()
requires true
ensures true;
{
	int x;
	loop(x);
}

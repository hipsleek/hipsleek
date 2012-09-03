void loop (int x)
requires true
ensures true;
{
	loop(x-1);
	loop(x+1);
}

template int r(int x).

void loop (int x)
infer [r]
requires Term[r(x)]
ensures true;
{
	int z = x + 1;	
	if (z > 0)
		loop(x-1); // loop(x+1);
	else if (z == 0)
		loop(x-1); // loop(x-1);
	else return;
}

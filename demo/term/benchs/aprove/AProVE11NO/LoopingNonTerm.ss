void main ()
requires MayLoop
ensures true;
{
	int i = 0;
	int j = length();
	loop(i, j);
}

void loop (ref int i, ref int j)
case {
	i>=j -> requires Term ensures true;
	i<j -> requires MayLoop ensures true;
}
{
	if (i < j) {
		i += length();
		loop(i, j);
	}
}

int length () 
requires Term
ensures res>=0;

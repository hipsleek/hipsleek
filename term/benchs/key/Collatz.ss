void collatz (int i)
case {
	i<=1 -> requires Term ensures true;
	i>1 -> requires MayLoop ensures true;	
}
{
	if (i > 1) {
		if (i%2 == 0) 
			i = i/2;
		else
			i = 3*i + 1;
		collatz(i);
	}
}

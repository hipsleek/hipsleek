int fib (int x)
case {
	x<0 -> requires Loop ensures false;
	x=0 | x=1 -> requires Term ensures true;
	x>1 -> requires Term[x] ensures true;
}
{
	if (x == 0)
		return 0;
	else if (x == 1)
		return 1;
	else
		return fib(x-1) + fib(x-2);
}

int rand_nat ()
requires Term
ensures res>0;

void main ()
requires Term
ensures true;
{
	fib(rand_nat());
}

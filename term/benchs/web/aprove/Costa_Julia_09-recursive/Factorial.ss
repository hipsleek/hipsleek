int fact (int n)
case {
	n<0 -> requires Term ensures true;
	n>=0 -> requires Term[n] ensures true;
}
{
	if (n < 0)
		return 1;
	else
		return n * fact(n - 1);
}

void main ()
requires Term
ensures true;
{
	fact(10);
}

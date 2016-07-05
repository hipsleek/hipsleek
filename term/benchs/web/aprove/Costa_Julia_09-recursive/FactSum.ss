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

int doSum (int n)
requires Term 
ensures true;
{
	int s = 0;
	while (n >= 0)
	case {
		n<0 -> requires Term ensures true;
		n>=0 -> requires Term[n] ensures true;
	}
	{
		s = s + fact(n);
		n = n - 1;
	}
	return s;
}

void main ()
requires Term
ensures true;
{
	fact(10);
}

void m (int n)
requires Term
ensures true;
{
	int i;
	while (i < n)
	case {
		i>=n -> requires Term ensures true;
		i<n -> requires Term[n-i] ensures true;
	}
	{ i++; }
}

void main ()
requires Term
ensures true;
{
	m(10);
}

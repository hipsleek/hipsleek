int ack (int m, int n)
case {
	m<=0 -> requires Term ensures true;
	m>0 -> case {
		n<=0 -> requires Term[m] ensures true;
		n>0 -> requires Term[m, n] ensures true;
	}
}
{
	if (m <= 0) 
		return n + 1;
	else if (n <= 0) 
		return ack(m - 1, 1);
	else 
		return ack(m - 1, ack(m, n - 1));
}

void main ()
requires Term
ensures true;
{
	ack(10, 12);
}

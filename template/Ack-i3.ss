template int r(int n, int m).

int ack (int m, int n)
  requires m>=0 & n>=0 & Term[m, n] ensures res>0;
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

template int r(int m, int n).

int ack (int m, int n)
infer [r]
requires m>=0 & n>=0 & Term[r(m, n)]
ensures true;
{
	if (m == 0) return n+1;
	else if (n == 0) return ack(m-1, 1);
	else return ack(m-1, ack(m, n-1));
}

int fact (int n)
requires true
ensures true;
{
	if (n == 0) return 1;
	else return n*fact(n+1);
}

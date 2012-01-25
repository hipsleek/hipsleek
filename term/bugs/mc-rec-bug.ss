
// TODO : termination bug below since
// 101-n is not decreasing for n=91 !!!
int mcCarthy (int n)
case {
	n>100 -> requires Term ensures res=n-10;
	n<=100 -> requires Term[101-n] ensures res=91;
}
{
	if (n > 100)
		return n - 10;
	else {
		int m = mcCarthy(n+11);
		return mcCarthy(m);
	}
}

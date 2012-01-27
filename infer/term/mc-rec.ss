ranking term_f(int n). 

int mcCarthy (int n)
infer[term_f]
case {
	n>100 -> requires Term ensures res=n-10;
	n<=100 -> requires Term[term_f(n)] ensures res=91;
}
{
	if (n > 100)
		return n - 10;
	else {
		int m = mcCarthy(n+11);
		return mcCarthy(m);
	}
}

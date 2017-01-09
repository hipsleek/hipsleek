relation zeros(int[] a, int[]b, int i, int j) == 
forall (k : (k < i & a[k] = b[k] | k > j & a[k] = b[k] | i <= k & k <= j & a[k] = 0)).


void mark(ref int[] x,int i,int l)
requires [k,t] dom(x,k,t) & k <= i & l <= t
ensures dom(x',k,t)& zeros(x',x,i,l);
{
	if (i <= l)
	{
		x[i] = 0;
		mark(x,i+1,l);
	}
}

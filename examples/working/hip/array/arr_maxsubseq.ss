/**
 Example: Array for dynamic programming
 **/

relation sumarray(int[] a, int i, int j, int s) == (i > j & s = 0 | i <= j & ex ( t : sumarray(a,i+1,j,t) & s = t + a[i])).

relation maxsubsum(int[] a, int i, int j, int s) == 
     (i > j & s = 0 | forall(k,t,h: (!(i <= k & k <= t & t <= j & sumarray(a, k, t, h)) | h <= s))).

// find the maximum of { a[i] + a[i+1] + ... + a[j] : 1 <= i, j <= n }
// for simplicity, the array a[1..n] is indexed from 1
// recursive: find the maximum of subsequence with j = n and j < n
int maxsubseq_rec(int [] a, int n)
	requires [l,h] dom(a,l,h) & l <= 1 & n <= h
	ensures maxsubsum(a,1,n,res);
{
	int m = 0;
	if (n > 0) {
		int i = n;
		m = maxsubseq_rec(a,n-1);
		int s = 0;
		while (i > 0)
		{
			s = s + a[i];
			if (s > m) m = s;
			i = i - 1;
		}
	}
	return m;
}

/*int maxsubsequencesum(int[] a, int n)
	requires true
	ensures maxsubsum(a,0,n-1,res);
{
	int m = 0; // maximum possible sum
	int t = 0; // a candidate maximum sum
	int k = 0; // running variable
	while (k < n)
		requires true
		ensures k' = n & maxsubsum(a,0,k-1,m);
	{
		int h = t + a[k];
		if (h < 0)
			t = 0;
		else if (h > m)
		{
			m = h;
			t = h;
		}
		k = k + 1;
	}
	return m;
}*/

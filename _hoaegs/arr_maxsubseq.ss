/**
 Example: Array for dynamic programming
 **/

relation sumarray(int[] a, int i, int j, int s) == (i > j & s = 0 | i <= j & ex ( t : sumarray(a,i+1,j,t) & s = t + a[i])).

relation maxsubsum(int[] a, int i, int j, int s) == (i > j & s = 0 | forall(k,t,h: (!(i <= k & k <= t & t <= j & sumarray(a, k, t, h)) | h <= s))).

int maxsubsequencesum(int[] a, int n)
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
}

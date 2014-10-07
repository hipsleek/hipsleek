/**
 Example: merge two arrays.
 **/

relation sorted(int[] a, int i, int j) == (i >= j | i < j & a[i] < a[i+1] & sorted(a,i+1,j)).

void merge(int[] a, int n, int[] b, int m, ref int[] c)
	requires sorted(a,0,n-1) & sorted(b,0,m-1)
	ensures sorted(c',0,n+m-1);
{
	int i = 0;
	int j = 0;
	int k = 0;
	while (i < n || j < m)
		requires 0<=i & i<=n & 0<=j & j<=m & k=i+j & sorted(c,0,i+j-1) 
		& (k = 0 | (j=m | j<m & c[k-1]<=b[j]) & (i=n | i<n & c[k-1]<=a[i]))
		ensures i'=n & j'=m & sorted(c',0,i'+j'-1);
	{
		if (j == m)
		{
			c[k] = a[i];
			i = i + 1;
		}
		else if (i == n || a[i] >= b[j]) // j < m
		{
			c[k] = b[j];
			j = j + 1;
		}
		else // i < n & j < m & a[i] < b[j]
		{
			c[k] = a[i];
			i = i + 1;
		}
		k = k + 1;
	}
}

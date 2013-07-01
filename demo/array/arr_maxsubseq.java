/**
 * Solve the maximum subsequence problem using DP.
 * 
 * TODO Implemented.
 * 
 * @author Vu An Hoa
 */

// s is sum a[i..j]
relation sumarray(int[] a, int i, int j, int s) == 
	(i > j & s = 0 | i <= j & sumarray(a,i+1,j,s - a[i])).

// s is a sum of some sub-range [u..v] of [i..j]
relation issubsum(int[] a, int i, int j, int s) ==
	ex(u,v : i <= u & u <= j & i <= v & v <= j & sumarray(a,u,v,s)).

// s is the maximum possible sum of a contiguous subsequence of a[i..j]	
relation maxsubsum(int[] a, int i, int j, int s) == 
	ex(u,v : i <= u & u <= j & i <= v & v <= j & sumarray(a,u,v,s)) & 
	forall(k,t,h: !(i <= k & k <= j & i <= t & t <= j & sumarray(a, k, t, h)) | h <= s).


// find the maximum of {a[i] + a[i+1] + ... + a[j] : 1 <= i, j <= n}
// for simplicity, the array a[1..n] is indexed from 1
// recursive: find the maximum of subsequence with j = n and j < n
int maxsubseq_rec(int [] a, int n)
	requires dom(a,1,n) & 1 <= n//[l,h] dom(a,l,h) & l <= 1 & n <= h
	ensures maxsubsum(a,1,n,res);
{
	assume n = 1;
	if (n==1) {
		assert maxsubsum(a,1,1,a[1]);
		return a[1];
	} else {
		int m = maxsubseq_rec(a,n-1);
		int i = n;
		int s = 0;
		while (i > 0)
			requires dom(a,1,n) & 0 < i <= n
			ensures maxsubsum(a,1,n,m');
		{
			s = s + a[i];
			if (s > m) m = s;
			i = i - 1;
		}
		return m;
	}
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

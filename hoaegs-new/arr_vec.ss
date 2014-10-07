/**
 Example: array initialization.
 **/

// Two array are identical except between i & j
relation identicalout(int[] a, int[] b, int i, int j) == forall(k : (i<=k & k<=j | a[k] = b[k])).

relation sumarrayvector(int[] c, int[] a, int[] b, int i, int j) == (i > j | forall ( k : (k < i | k > j | i <= k & k <= j & c[k] = a[k] + b[k]))).

relation prodarrayvector(int[] c, int[] a, int[] b, int i, int j) == (i > j | forall ( k : (k < i | k > j | i <= k & k <= j & c[k] = a[k] * b[k]))).

//relation sumarray(int[] a, int i, int j, int s) == (i > j & s = 0 | i <= j & ex ( t : sumarray(a,i+1,j,t) & s = t + a[i])).
relation sumarray(int[] a, int i, int j, int s) == (i > j & s = 0 | i <= j & ex ( t : sumarray(a,i,j-1,t) & s = t + a[j])).

relation partial_sum(int[] c, int[] a, int i, int j) == (i > j | forall ( k : (k < i | k > j | k = i & c[k] = a[k] | i < k & k <= j & c[k] = c[k-1] + a[k]))).
//this formulation does not work with both right/left recursive sumarray!
//relation partial_sum(int[] c, int[] a, int i, int j) == (i > j | forall ( k : (k < i | k > j | i <= k & k <= j & sumarray(a,i,k,c[k])))).

relation differfrom(int[] a, int[] b, int i, int j, int d) == (i > j | forall ( k : (k < i | k > j | i <= k & k <= j & a[k] - b[k] = d))).

void vecsum(int[] a, int[] b, int n, int[]@R c)
	requires true
	ensures sumarrayvector(c',a,b,0,n-1) & identicalout(c',c,0,n-1);
{
	if (n > 0)
	{
		c[n-1] = a[n-1] + b[n-1];
		vecsum(a,b,n-1,c);
	}
}

void vecprod(int[] a, int[] b, int n, int[]@R c)
	requires true
	ensures prodarrayvector(c',a,b,0,n-1) & identicalout(c',c,0,n-1);
{
	if (n > 0)
	{
		c[n-1] = a[n-1] * b[n-1];
		vecprod(a,b,n-1,c);
	}
}

void increaseall(int[]@R a, int i, int j, int d)
	requires true
	ensures differfrom(a',a,i,j,d) & identicalout(a',a,i,j);
{
	if (i <= j)
	{
		a[i] = a[i] + d;
		increaseall(a,i+1,j,d);
	}
}

void vecpartialsum(int[] a, int i, int j, int[]@R c)
	requires true
	ensures partial_sum(c',a,i,j) & identicalout(c',c,i,j);
{
	if (i <= j)
	{
		c[i] = a[i];
		vecpartialsum(a,i+1,j,c);
		increaseall(c,i+1,j,a[i]);
	}
}

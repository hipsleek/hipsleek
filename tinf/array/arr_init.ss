/**
 Example: array initialization.
 **/
 
relation zeros(int[] a, int i, int j) == (i > j | forall ( k : (k < i | k > j | i <= k & k <= j & a[k] = 0))).

/* a and b are identical except a[k] = 0 for all i <= k <= j */ 
relation identicalzeroes(int[] a, int[] b, int i, int j) == forall ( k : (k < i & a[k] = b[k] | k > j & a[k] = b[k] | i <= k & k <= j & a[k] = 0)).
  /*
void initright(ref int[] a, int i, int j) 
	requires true
	ensures identicalzeroes(a',a,i,j); /* zeros(a', i, j); ==> missing condition: a'[k] = a[k] for k < i | k > j */
{
	if (i <= j)
	{
		a[i] = 0;
		initright(a,i + 1,j);
	}
}
*/
void initloop(ref int[] a, int i, int j) 
	requires 0 <= i & 0 <= j & i <= j
	ensures zeros(a', i, j);
{
	int k = i;
	while (k <= j) 
		requires i<=k & k<=j+1 & zeros(a,i,k-1)
		ensures k'=j+1 & zeros(a',i,k'-1);
	{
		a[k] = 0;
		k = k + 1;
	}
}
/*
void initleft(ref int[] a, int i, int j) 
	requires true
	ensures identicalzeroes(a',a,i,j);
{
       	if (i <= j)
	{
         a[j] = 0;
		initleft(a, i, j-1);
	}
}
*/


/**
 * Find the sum of the elements of an array. This examples
 * show two ways of computing the sum and illustrates the use
 * of induction.
 * 
 * @author Vu An Hoa
 */

relation dom(int[] a, int low, int high) == 
	(dom(a,low-1,high) | dom(a,low,high+1)).

relation sumarray(int[] a, int i, int j, int s) == 
	(i > j & s = 0 | i = j & s = a[i] | i < j & sumarray(a,i+1,j,s-a[i])).

int sigmaright(int[] a, int i, int j) 
	requires [t,k] dom(a,t,k) & t <= i & j <= k /* the allocation is from a[i..j] */
	ensures sumarray(a,i,j,res);
{
	if (i > j)
		return 0;
	else 
	{
		return a[i] + sigmaright(a, i+1, j);
	}
}


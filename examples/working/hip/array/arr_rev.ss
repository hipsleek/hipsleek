/**
 * Array reversing
 * 
 * @author Vu An Hoa
 */

relation idexc(int[] a, int[] b, int i, int j) == 
	forall(k : (i<=k & k<=j | a[k] = b[k])).

relation reversearr(int[] a, int[] b, int i, int j) == 
	(i > j | forall(k : (k < i | k > j | a[k] = b[j + i - k]))).

void arrayrev(ref int[] a, int i, int j)
	requires [k,t] dom(a,k,t) & k <= i & j <= t
	ensures reversearr(a',a,i,j) & idexc(a',a,i,j);
{
	if (i <= j)
	{
		int temp = a[i];
		a[i] = a[j];
		a[j] = temp;
		arrayrev(a,i+1,j-1);
	}
}

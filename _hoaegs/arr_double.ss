/**
 Example: Array doubling
 **/

relation idexc(int[] a, int[] b, int i, int j) == forall(k : (i<=k & k<=j | a[k] = b[k])).

relation doubleof(int[] a, int[] b, int i, int j) == (i > j | forall(k : (k < i | k > j | a[k] = 2 * b[k]))).

void doublearr(ref int[] a, int i, int j)
	requires true
	ensures doubleof(a',a,i,j) & idexc(a',a,i,j);
{
	if (i <= j)
	{
		a[i] = 2 * a[i];
		doublearr(a,i+1,j);
	}
}

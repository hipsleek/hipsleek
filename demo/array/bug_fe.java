/**
 * inverting the indices
 * 
 */

relation dom(int[] a, int low, int high) == 
	(dom(a,low-1,high) | dom(a,low,high+1)).

// why failure explanation has an error here?

void swap (ref int[] a, int i, int j)

    requires [t,k] dom(a,t,k) & t <= i &  i <= k & t <= j & j <= k 
	ensures dom(a',t,k);
{
    int t = a[i];
    a[i] = a[j];
    a[j] = t;
}

/**
 Example: array modification.
 **/

relation sorted(int[] a, int i, int j) == (i >= j | i < j & a[i] < a[i+1] & sorted(a,i+1,j)).

void insertion_sort(int[] a, int n)
	requires true
	ensures sorted(a,0,n-1);
{
}

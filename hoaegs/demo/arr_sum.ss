/**
 Example: sum of elements of an array.
 **/

// right recursive definition of the sum
relation sumarray(int[] a, int i, int j, int s) == 
		(i > j & s = 0 | i <= j & sumarray(a,i+1,j,s - a[i])).

int compute_sum_array(int[] a, int i, int j) 
	requires true
	ensures sumarray(a, i, j, res);
{
	if (i > j)
		return 0;
	else 
		return a[i] + compute_sum_array(a, i+1, j);
}

/**
 Example: maximum value of the array.
 **/

relation nonzero(int a) == exists (b : b < a).

relation upperbnd(int[] a, int i, int j, int s) == (i > j | forall ( k : (k < i | k > j | i <= k & k <= j & a[k] <= s))).  

// relation upper_bound_array(int[] a, int i, int j, int s) == (i > j | i <= j & a[i] <= s & upper_bound_array(a,i+1,j,s)).

int max_value_of_array(int[] a, int i, int j) 
	requires dom(a,i,j) & i <= j
	ensures upperbnd(a, i, j, res);
{
	assume dom(a',i,j); 
    if (i == j)
		return a[i];
	else {
			int m = max_value_of_array(a,i+1,j);
			if (m > a[i])
				return m;
			else
				return a[i];
        }
}
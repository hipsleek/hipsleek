/**
 Example: maximum value of the array.
 **/

relation nonzero(int a) == exists (b : b < a).

relation upperbnd(int[] a, int i, int j, int s) == (i > j | forall ( k : (k < i | k > j | i <= k & k <= j & a[k] <= s))).  

// relation upper_bound_array(int[] a, int i, int j, int s) == (i > j | i <= j & a[i] <= s & upper_bound_array(a,i+1,j,s)).


int max_array_val(int[] a, int i, int j)
	requires i <= j
	ensures upperbnd(a,i,j,res);
{
	int m = a[j];
	int k = j;
	while (i <= k)
		requires i-1 <= k & upperbnd(a,k+1,j,m)
		ensures k'= i-1 & upperbnd(a,k'+1,j,m'); 
	{
		if (a[k] > m) {
			m = a[k];
		}
		k = k - 1;
	}
	return m;
}

int max_value_of_array(int[] a, int i, int j) 
	requires i <= j
	ensures upperbnd(a, i, j, res);
{
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
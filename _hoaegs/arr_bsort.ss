/**
 Example: Bubble sort
 **/

relation sorted(int[] a, int i, int j) == (i >= j | forall (k : (k < i | k >= j | a[k] <= a[k+1]))).

// Go through array a[i..j] once and swap adjacent 
// elements if they are out of increasing order
// return true if no swap is required (in such case
// a[i..j] must be sorted; and false otherwise
bool bubble(ref int[] a , int i , int j)
	requires true
	ensures (!res | sorted(a,i,j) & a' = a);
{
	if (i < j)
	{
		if (a[i] > a[i+1])
		{
			int t = a[i];
			a[i] = a[i+1];
			a[i+1] = t;
			bubble(a,i+1,j);
			return false;
		}
		else return bubble(a,i+1,j);
	}
	else
		return true;
}

// Sort the array using bubble sort algorithm: Transpose
// adjacent elements until no transposition is required.
void bubblesort(ref int[] a, int i, int j)
	requires true
	ensures sorted(a', i, j);
{
	if (!bubble(a, i, j)) bubblesort(a, i, j);
}

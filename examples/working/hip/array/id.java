/**
 * inverting the indices
 * 
 */

// relation dom(int[] a, int low, int high) == 
// 	(dom(a,low-1,high) | dom(a,low,high+1)).

relation bnd(int[] a, int i, int j, int low, int high) == 
 	(i > j | i<=j & forall ( k : (k < i | k > j | low <= a[k] <= high))).

relation idexc(int[] a, int[] b, int i, int j) == 
	forall(k : (i<=k & k<=j | a[k] = b[k])).

// relation bnd(int[] a, int i, int j, int low, int high) == 
// 	bnd(a,i-1,j+1,low,high).

// bnd(a,i,j,low,high) & i<=s & b<=j  => bnd(a,s,b,low,high)
void invert(ref int[] a, int i, int j, int low, int high) 
    requires [t,k] dom(a,t,k) & t <= i & j <= k
    case {
      i>=j -> ensures dom(a',t,k) & a'=a; 
      i<j -> ensures dom(a',t,k) & idexc(a,a',i,j);
    }

{
	if (i<j) {
        swap(a,i,j);
        invert(a,i+1,j-1,low,high);
    }
}


void swap (ref int[] a, int i, int j)
    requires [t,k] dom(a,t,k) & t <= i &  i <= k & t <= j & j <= k 
    ensures (exists b: dom(a',t,k) & update_array(a,i,a[j],b) & update_array(b,j,a[i],a'));
{
    int t = a[i];
    a[i] = a[j];
    a[j] = t;
}

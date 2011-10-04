/**
 * Find the sum of the elements of an array. This examples
 * show two ways of computing the sum and illustrates the use
 * of induction.
 * 
 * @author Vu An Hoa
 */

relation dom(int[] a, int low, int high) == 
	(dom(a,low-1,high) | dom(a,low,high+1)).


int access (int[] a, int i) 
	requires [t,k] dom(a,t,k) 
             & t <= i & i <= k /* the allocation is from a[i..j] */
	ensures res=a[i];
{
	return a[i];
}


void swap (ref int[] a, int i, int j) 
	requires [t,k] dom(a,t,k) & t <= i &  i <= k & t <= j & j <= k  
            /* the allocation is from a[i..j] */
	ensures a'[i]=a[j] & a'[j]=a[i] & 
       forall(m: m=i | m=j | a'[m]=a[m] ) ; //'
{
    int t = a[i];
    a[i] = a[j];
    a[j] = t;
}


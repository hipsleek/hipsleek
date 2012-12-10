/**
 * inverting the indices
 * 
 */

/*

Exception occurred: Failure("couldn't infer type for b_40 in ; (i int); (j int); (res void); (a int[])\n, could it be an unused var?\n")
 */

void swap (ref int[] a, int i, int j)
    // requires [t,k] dom(a,t,k) & t <= i &  i <= k & t <= j & j <= k 
	// ensures dom(a',t,k);//'
    requires true
    ensures true & exists (b:update_array(a,i,a[j],b) & update_array(b,j,a[i],a')); //'
   requires true
   ensures (exists c:update_array(a,i,a[j],c) & update_array(c,j,a[i],a')); //'
{
    int t = a[i];
    a[i] = a[j];
    a[j] = t;
}

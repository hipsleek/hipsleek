/**
 * inverting the indices
 * 
 */

relation dom(int[] a, int low, int high) == 
	(dom(a,low-1,high) | dom(a,low,high+1)).

relation bnd(int[] a, int i, int j, int low, int high) == 
 	(i > j 
   | i=j & low <= a[i] <= high 
   | i<=j &  low <= a[i] <= high & bnd(a,i+1,j,low,high)
   | i<=j &  low <= a[j] <= high & bnd(a,i,j-1,low,high)
    ).

    //relation bnd(int[] a, int i, int j, int low, int high) == 
	//bnd(a,i-1,j+1,low,high).

// bnd(a,i,j,low,high) & i<=s & b<=j  => bnd(a,s,b,low,high)
void invert(ref int[] a, int i, int j
            , int low, int high
            ) 
    /*
	requires dom(a,i,j) 
       & bnd(a,i,j,low,high) 
	ensures dom(a',i,j) //'
       & bnd(a',i,j,low,high) 
    ;
    */
	requires 
    //[low,high]
     dom(a,i,j) & bnd(a,i,j,low,high) 
    case {
      i>=j -> ensures a'=a & dom(a',i,j) & bnd(a',i,j,low,high); //'
      i<j -> ensures dom(a',i,j) //'
                         //& bnd(a',i,j,low,high) 
        ;//'
    }

{
	if (i<j) {
        swap(a,i,j);
        invert(a,i+1,j-1
               ,low,high
        );
    }
}


void swap (ref int[] a, int i, int j) 
    requires [t,k] dom(a,t,k) & t <= i &  i <= k & t <= j & j <= k 
            //& bnd(a,t,k,low,high) 
            /* the allocation is from a[i..j] */
	ensures dom(a',t,k) & a'[i]=a[j] & a'[j]=a[i] & 
       forall(m: m=i | m=j | a'[m]=a[m] ) //'
            //& bnd(a',t,k,low,high)//'
       ;
{
    int t = a[i];
    a[i] = a[j];
    a[j] = t;
}

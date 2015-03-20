/*int main()
  requires true
  ensures true;
{
  int[] a;
	while (a[1+2] > 0)
          requires [k,t] dom(a,k,t)true
            ensures a[3]<0 & flow __flow;
        {
		a[3] = a[2+1] - 1;
        }
        /*int b;
        while (b>0)
          requires true
            ensures b<0 & flow __flow;
        {
          b = b - 1;
          }*/
	return 0;
}
*/
relation at_equal(int[] a,int i,int j,int p,int v) == (i>j| i>p | j<p |i<=p & p<=j & a[p] = v).
relation at_greater(int[] a,int i,int j,int p,int v) == (i>j| i>p | j<p |i<=p & p<=j & a[p] > v).
relation at_less(int[] a,int i,int j,int p,int v) == (i>j| i>p | j<p |i<=p & p<=j & a[p] < v).
relation decrease_by_one(int[] a,int[] new_a,int i,int j,int p) == (i>j| i>p | j<p |i<=p & p<=j & new_a[p] = a[p]-1).

  int[] array_allocate(int i,int j)
  requires [k,t] dom(a,k,t) & k <= i & j <= t & i<=p<=j
  ensures dom(res,k,t) &  k <= i & j <= t ;

void update_array(ref int[] a,int i,int j,int p,int v)
  requires [k,t] dom(a,k,t) & k <= i & j <= t & i<=p<=j
  ensures dom(a',k,t) & at_equal(a',i,j,p,v);

void array_decrease(ref int[] a,int i,int j,int p)
     requires [k,t] dom(a,k,t) & k <= i & j <= t & i<=p<=j
     ensures dom(a',k,t) & decrease_by_one(a,a',i,j,p);

int[] aalloc(int dim) 
	requires true 
	ensures dom(res,0,dim-1);

                               /*
void while_array(ref int[] a, int i,int j)
  requires [k,t] dom(a,k,t) & i=0 & j=5 & k <= i & j <= t & at_greater(a,i,j,3,0)
     ensures dom(a',k,t) & at_equal(a',i,j,3,0);
{
  //assert at_greater(a,i,j,3,0);
  //update_array(a,i,j,3,0);
  //assert at_equal(a',i,j,3,0);
  array_decrease(a,i,j,3);
  if(a[3]>0){
    while_array(a,i,j);
  }
}
                               */
/*
void while_array_old(ref int[] a, int i,int j)
  requires [k,t] dom(a,k,t) & i=0 & j=5 & k <= i & j <= t & a[3]>0
     ensures dom(a',k,t) & a[3]=0;
{
  //assert at_greater(a,i,j,3,0);
  //update_array(a,i,j,3,0);
  //assert at_equal(a',i,j,3,0);
            
  a[3] = a[3] -1;
  if(a[3]>0){
    while_array(a,i,j);
  }
}
*/
void loop(ref int[] a, int i,int j)
  requires [k,t] dom(a,k,t) & i=0 & j=5 & k <= i & j <= t
     ensures dom(a',k,t) & at_equal(a',i,j,3,0)  | dom(a',k,t) & at_less(a',i,j,3,0);
{
    while(a[3]>0)
      requires [k,t] dom(a,k,t) & i=0 & j=5 & k <= i & j <= t
       ensures dom(a',k,t) & at_equal(a',i,j,3,0) | dom(a',k,t) & at_less(a',i,j,3,0) ;
    {
      update_array(a,i,j,3,a[3]-1);
      //array_decrease(a,i,j,3);
    }

}

int main()
  requires true
  ensures true;
{
  int[] a;
  a = aalloc(10);
  dprint;
  int i;
  int j;
  i=0;
  j=10;
	while (a[2+1] > 0)
          requires [k,t] dom(a,k,t) & i=0 & j=5 & k <= i & j <= t
            ensures dom(a',k,t) & at_equal(a',i,j,3,0) | dom(a',k,t) & at_less(a',i,j,3,0) ;
        {
          //array_decrease(a,i,j,3);
          update_array(a,i,j,3,a[3]-1);
		
        }
	return 0;
}

/*
int main()
  requires true
  ensures true;
{
  int[] a;
  a = array_allocate(0,10);
  while_array(a,0,10);
  return 0;
}
*/

void simple_array(int[] a,int i,int j)
  requires [k,t] dom(a,k,t) & i=0 & j=5 & k <= i & j <= t
     ensures dom(a',k,t);
{
  a[3] = 5;
}

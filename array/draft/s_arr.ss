relation update_array(int[] a, int[] r, int i, int v).

int[] update_arr( int[] a, int i, int v)
  requires true
  ensures update_array(a,res,v,i);

int array_get(int[] a, int i) 
   requires true 
   ensures res = a[i];

int foo(int x)
  requires true
  ensures res=x;
{
  int[] a;
  a = update_arr(a,5,x);
  int r = array_get(a,5);
  dprint;
  return r;

}

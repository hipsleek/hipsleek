//relation update_array(int[] a, int[] r, int v, int i).
// Any relation with prefix of "update_array" will be translated into "store".

/*
  int[] update_arr(int[] a, int i, int v)
  requires true
  ensures update_array(a,res,v,i);

int array_get(int[] a, int i) 
   requires true 
   ensures res = a[i];
// a[i] will be translated into "select"

*/

// !!!! This function need to use -prelude "prelude_aux.ss" 
int foo(int x,ref int[] a)
// requires true
//ensures res=x+1;
  requires true
  ensures a'[5]=x & res=x+1;
{
  int[] a;
  //a = update_arr(a,5,x+1);
  a[5] = x;
  //a = update___1d(x+1,a,5);
  int r;
  r = x+1;
  //dprint;
  return r;

}


// !!!! This function need to use -prelude "prelude_aux.ss" 
int foo(int x)
  infer[@post_n]
  requires true
//ensures res=x+1;
  ensures true;
{
  int[] a;
  int i =5;
  a[i] = x+1;
  int r;
  r = a[i];
  return r;

}

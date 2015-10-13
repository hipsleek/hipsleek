// !!!! This function need to use -prelude "prelude_aux.ss" 
int foo(int x)
  infer[@term]
  requires true
  ensures res=x+1;
{
  int[] a;
  a[5] = x+1;
  int r;
  r = a[5];
  return r;

}

// addr-of operator

// how come we don't use pass-by-copy here?
// pass-by-copy only for struct?
// how about struct*, do we use pass-by-copy?
int foo(int* q)
/*@
  requires q::int*<a>
  ensures q::int*<a+1> & res=a+1;
*/
{
  int r = (*q)+1;
  *q = r;
  return r;
}

int main()
/*@
  requires true
  ensures res=3;
*/
{
  int x;
  x = 2;
  int r=foo(&x);
  return r;
}



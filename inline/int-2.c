// addr-of operator
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
  x=5;
  int* r = &x;
  x=2;
  int t=foo(r);
  int k=x+1;
  return x;
}



// addr-of operator
// how come we don't use pass-by-copy here?
// pass-by-copy only for struct?
// how about struct*, do we use pass-by-copy?
int foo(int** q)
/*@
//  requires q::int__star__star<r>*r::int__star<a>
//  ensures q::int__star__star<r>*r::int__star<a+1> & res=a+1;
//  requires q::int__star^<a>
//  ensures q::int__star^<a+1> & res=a+1;
  requires q::int^^<a>
  ensures q::int^^<a+1> & res=a+1;
*/
{
  int* r = *q;
  *r = *r+1;
  return *r;
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
  int t=foo(&r);
  int k=x+1;
  return x;
}



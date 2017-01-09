int a;

int foo(int* x)
/*@
  requires x::int^<n>
  ensures x::int^<n+1> & res = n+2;
*/
{
  *x = *x+1;
  return *x + 1;
}


void main()
/*@
  requires true
  ensures a' = 3;
*/
{
  a = 1;
  a = foo(&a);
}

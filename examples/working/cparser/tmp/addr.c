int a;

void foo(int* x)
/*@
  requires x::int^<n>
  ensures x::int^<2>;
*/
{
  *x = 2;
}


void main()
/*@
  requires true
  ensures a' = 2;
*/
{
  a = 1;
  foo(&a);
}

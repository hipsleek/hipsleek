int a;

void foo(int* x)
/*@
  requires x::int^<n>
  ensures x::int^<n+1>;
*/
{
  *x = *x+1;
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

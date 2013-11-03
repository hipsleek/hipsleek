#include<stdio.h>
// addr-of operator
int foo(int* q)
/*@
  requires q::int*<a>
  ensures q::int*<a+1> & res=a+1;
*/
{
  int* r = q;
  *r = (*r)+1;
  return *r;
}

int main()
/*@
  requires true
  ensures res=3;
*/
{
  int x;
  x=2;
  int t=foo(&x);
//  printf("foo(x) ==> %i\n",t);
//  printf("x ==> %i\n",x);
  return x;
}



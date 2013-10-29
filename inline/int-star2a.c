#include<stdio.h>
// addr-of operator
// how come we don't use pass-by-copy here?
// pass-by-copy only for struct?
// how about struct*, do we use pass-by-copy?
int foo(int** q)
/*@
  requires q^::int*<a>
  ensures q^::int*<a+1> & res=a+1;
  //  requires q::int__star__star<r>*r::int__star<a>
  //  ensures q::int__star__star<r>*r::int__star<a+1> & res=a+1;
  //  requires q::int__star^<a>
  //  ensures q::int__star^<a+1> & res=a+1;
*/
{
  int* r = *q;
  *r = *r+1;
  return *r;
};

struct pair {
  int x;
  int y;
};

int main()
/*@
  requires true
  ensures res=4;
*/
{
  int x;
  x=5;
  int* r = &x;
  x=2;
  int t=foo(&r);
  int k=x+1;
  x=x+1;
  //printf("foo(&r) = %i\n",t); ///3
  //printf("x = %i\n",x); //4
  return x;
}



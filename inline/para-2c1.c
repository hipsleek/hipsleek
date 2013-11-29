#include<stdio.h>
// addr-of operator
struct pair {
  int x;
  int y;
};

int foo(struct pair q)
/*@
  requires q::pair<a,b>
  ensures q::pair<a,b> & res=a+b;
*/
{
  struct pair p = q;
  p.x = q.x+1;
  p.x = q.x+q.y;
  return p.x;
}

int main()
/*@
  requires true
  ensures res=2;
*/
{
  struct pair p;
  p.x = 1;
  p.y = 2;
  int t=foo(p);
  //printf("foo(p) ==> %i\n",t); //4
  //printf("p.x ==> %i\n",p.x); //1
  return p.x;
}



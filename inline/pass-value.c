#include "../examples/working/cparser/stdhip.h"

struct pair {
  int x;
  int y;
};

int foo(struct pair q)
// pass by copy
/*@
  requires q::pair<a,_>
  ensures q::pair<a,_> & res=a;
*/
{
  return q.x;
}

int foo2(struct pair q)
// pass by ptr
/*@
  requires q::pair<a,_>@L
  ensures res=a;
*/
{
  return q.x;
}


int goo(struct pair* q)
// pass by copy
/*@
  requires q::pair<a,b>
  ensures q::pair<a,b> & res=a;
*/
{
  return q->x;
}

int hoo()
/* 
  requires true
  ensures res=5;
*/
{
  struct pair p;
  p.x = 2; 
  int t=foo(p);
  struct pair* pp;
  pp = malloc(sizeof (struct pair));
  int* iiii = malloc(1);
  pp->x =3;
  t=t+goo(pp);
  return t;
}



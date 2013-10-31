#include<stdio.h>
// inline fields

struct pair {
  int x;
  int y;
};

struct quad {
  struct pair p1;
  struct pair* p2;
};

int foo(struct quad* q)
/*@
  requires q::quad<a,b,p>@L * p::pair<c,d>@L
  ensures res=c+2;
*/
{
  int r = (*q).p2->x+2;
  return r;
}
/*
{local: int r
int r;
{r = (int)member access member access q~~>p2~~>x + 2;
(76, ):return r}}
}
*/

int main()
/*@
 requires true
  ensures res=6;
*/
{
  struct quad p;
  struct pair pp;
  pp.x = 4;
  p.p2 = &pp;
  p.p1.x = 3;
  int r=foo(&p);
  //printf("p.p1.x = %i\n",p.p2->x); // 4
  //printf("r = %i\n",r); //6
  return r;
}
/*
{local: quad p,pair pp,int r,int tmp
quad p = new quad(0, 0, null);
pair pp = new pair(0, 0);
int r;
int tmp;
{member access pp~~>x = 4;
member access p~~>p2 = pp;
member access p~~>p1~~>x = 3;
tmp = (84, ):foo(p);
r = tmp;
(86, ):return r}}

// why is there an intermdiate tmp introduced?
}
*/

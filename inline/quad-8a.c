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
int r = member access q~~>p1~~>x + 2;
(80, ):return r}
}

{local: int r
int r;
{r = (int)member access member access q~~>p1~~>x + 2;
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

}
/*

{
{local: quad p,int r
quad p = new quad(0, 0, null);
member access p~~>p1~~>x = 3;
int r = (76, ):foo(p);
(77, ):return r}
}

{
{local: quad p,int r,int tmp
quad p = new quad(null, null);
int r;
int tmp;
{member access member access p~~>p1~~>x = 3;
tmp = (81, ):foo(p);
r = tmp;
(83, ):return 0}}
}
*/



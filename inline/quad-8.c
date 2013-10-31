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
  requires q::quad<a,b,p>@L
  ensures res=a+2;
*/
{
  int r = (*q).p1.x+2;
  return r;
}
/*
{
{local: int r
int r;
{r = (int)member access member access q~~>p1~~>x + 2;
(76, ):return r}}
}
*/

int main()
/*@
 requires true
  ensures res=5;
*/
{
  struct quad p;
  p.p1.x = 3;
  int r=foo(&p);
  //printf("p.p1.x = %i\n",p.p1.x); // 3
  //printf("r = %i\n",r); //5

}
/*
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



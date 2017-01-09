#include<stdio.h>
struct pair {
	int x;
	int y;
};

int main() 
/*@
  requires true
  ensures res=2;
*/
{
  struct pair p;
  p.x = 1;
  struct pair* pp;
  pp = &p;
  pp->x = pp->x +1;
  //printf("*ppp->x = %i",(*ppp)->x);
  //printf("*pp->x = %i",pp->x);
  //printf("p.x = %i",p.x);
  return p.x;

}

/*
{
{local: pair p,pair pp
pair p = new pair(0, 0);
pair pp = new pair(0, 0);
          ^^^^^^^^^^^^^^ redundant
{member access p~~>x = 1;
pp = p;
member access pp~~>x = (int)member access pp~~>x + 1;
(78, ):return member access p~~>x}}
}
*/

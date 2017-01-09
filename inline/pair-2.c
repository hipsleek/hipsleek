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
  struct pair** ppp;
  ppp = &pp;
  (*ppp)->x = (*ppp)->x +1;
  //printf("*ppp->x = %i",(*ppp)->x);
  //printf("*pp->x = %i",pp->x);
  //printf("p.x = %i",p.x);
  return pp->x;

}

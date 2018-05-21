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

/*
int main()[]
static EBase: [][](htrue) * ([] & true)( FLOW __norm) {EAssume: 1,:(emp) * ([] & res = 2)( FLOW __norm)}
dynamic EBase: [][](hfalse) * ([] & false)( FLOW __false) 
{
{local: pair p,pair pp,pair_star ppp
pair p = new pair()
pair pp
pair_star ppp
{member access p~~>x = 1
member access pp~~>value = p
ppp = pp
member access member access ppp~~>value~~>x = (int)member access member access ppp~~>value~~>x + 1
(118, ):return member access member access pp~~>value~~>x}}
}


ERROR: at _0:0_0:0
Message: field name value is not found

*/

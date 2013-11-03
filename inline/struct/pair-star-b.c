#include<stdio.h>
// C-program below compile which
// suggest that foo and star_foo are equivalent.
// removing addr-of operator
struct pair {
  int x;
  int y;
};
 
int foo(struct pair** q)
/*@
  requires q::pair_star<r>*r::pair<a,b>
  ensures q::pair_star<null>*r::pair<a,b+2> & res=b+2;
*/
{
  (*q)->y=((*q)->y)+2;
  int t = (*q)->y;
  *q = 0;
  return t;
}


int main()
/*@
  requires true
  ensures res=5;
*/
{
  struct pair p;
  p.y = 3;
  struct pair* pp = &p;
  struct pair** ppp = &pp;
  int r=foo(ppp);
  //printf("p.y = %i\n",p.y); //5
  //printf("foo(ppp) = %i\n",r); //5
  //printf("pp = %i\n",pp); //null
  //printf("ppp = %i\n",ppp); //!=null
  //printf("pp->y = %i",pp->y);
  //pp->y=0;
  return r;
}

/*


{local: pair p,pair_star ppp,int r,int tmp,pair_star addr_pp
pair p = new pair(0, 0);
pair_star ppp;
int r;
int tmp;
pair_star addr_pp = new pair_star(null);
{member access p~~>y = 3;
member access addr_pp~~>deref = p;
ppp = addr_pp;
tmp = (93, ):foo(ppp);
r = tmp;
//member access member access addr_pp~~>deref~~>y = 0;
(98, ):return r}}
}

*/

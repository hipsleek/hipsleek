#include<stdio.h>
// C-program below compile which
// suggest that foo and star_foo are equivalent.
// removing addr-of operator
struct pair {
  int x;
  int y;
};
 
int foo(struct pair* q)
/*@
  requires q::pair<a,b>
  ensures q::pair<a,b> & res=b*2;
*/
{
  struct pair** qq = &q;
  int t = q->y;
  int r = (*qq)->y+t;
  //printf("t = %i\n",t); //5
  //printf("t = %i\n",r); //5
  return r;
}

/*
int foo(pair q)[]
pair_star qq;
int t;
int r;
pair_star addr_q = new pair_star(null); 
// missing assignment::  addr_q.deref = q;
{qq = addr_q;
t = member access member access addr_q~~>deref~~>y;
r = (int)member access member access qq~~>deref~~>y + t;
(79, ):return r}}
}

 */

void main()
{
  struct pair p;
  p.y=5;
  struct pair* pp = &p;
  foo(pp);
}

/*
{local: pair p,pair pp
pair p = new pair(0, 0);
pair pp;
{pp = p;
(74, ):foo(pp);
(75, ):return }}
}
*/

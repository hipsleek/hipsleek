//#include <stdlib.h>
#include "../examples/working/cparser/stdhip.h"
struct node {
  int val;
  struct node* next;
};

/*@
ll<n> == self=null & n=0
  or self::node<_,q>*q::ll<n-1>
inv n>=0.

lseg<p,n> == self=p   & n=0
  or self::node<_,q>*q::lseg<p,n-1>
inv n>=0.

cll<n> == self::node<_,q>*q::lseg<self,n-1>
inv n>=1;

lemma_safe self::lseg<p,n> <- self::lseg<q,m>*q::node<_,p> & n=m+1.

*/

struct node* new_lseg(struct node* p, int n)
  /*@
    requires n >=0
    ensures res::lseg<p,n>;
  */
{
  if (n==0)
    return p;
  struct node *x = malloc(sizeof *x);
  x->next = new_lseg(p, n-1);
  return x;
}

struct node* new_cll(int n)
  /*@  
    requires n>=1
    ensures res::cll<n>;
  */
{
  struct node *x = malloc(sizeof *x);
  x->next = new_lseg(x,n-1);
  return x;
}

void main()
  /*@
    requires true
    ensures false;
  */
{
  int n = 10;
  struct node *xs = new_cll(n);
  while (xs != NULL)
    /*@
      requires xs::cll<n>@L & Loop
      ensures false;
    */
  {
     xs = xs->next;
  }
}

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

struct node* new_ll(int n)
  /*@  
    requires n>=0
    ensures res::ll<n>;
  */
{
  if (n==0)
    return NULL;
  struct node *x = malloc(sizeof *x);
  x->next = new_ll(n-1);
  return x;
}

void main()
  /*@
    requires true
    ensures true;
  */
{
  struct node *xs = new_ll(10);
  while (1)
    /*@
      requires xs::ll<n>@L & Term[n]
      ensures true;
    */
  {
     if (xs == NULL)
       break;
     xs = xs->next;
  }
}

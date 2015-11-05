/*
 * Date: 30/09/2015
 * Created by: 
 *   Ton Chanh Le (chanhle@comp.nus.edu.sg) and
 *   Duc Muoi Tran (muoitranduc@gmail.com)
 */

#include <stdlib.h>

extern int __VERIFIER_nondet_int();

/*@
ll<n> == self=null & n=0
  or self::node<_,q>*q::ll<n-1>
inv n>=0.

lseg<p,n> == self=p   & n=0
  or self::node<_,q>*q::lseg<p,n-1>
inv n>=0.

cll<n> == self::lseg<q,n> & q = self
inv n>=0.

lemma_safe self::lseg<p,n> <- self::lseg<q,m>*q::node<_,p> & n=m+1.

lemma_safe self::lseg<p,n> & p=null <-> self::ll<n>.

*/

typedef struct node {
  int val;
  struct node* next;
} node_t;

// Create a new linked list with length n when n >= 0
// or non-terminating when n < 0 
node_t* new_ll(int n)
  /*@
    requires n >=0
    ensures res::ll<n>;
  */
{
  if (n == 0)
    return NULL;
  node_t* head = alloca(sizeof(node_t));
  head->val = n;
  head->next = new_ll(n-1);
  return head;
}

int length(node_t* xs)
  /*@
    requires xs::lseg<y,n>*y::ll<m>
    ensures true;
  */
{
  if (xs == NULL)
    return 0;
  return (1 + length(xs->next));
}

node_t* append(node_t* x, node_t* y)
  /*@
    requires x::ll<n>*y::ll<m>
    ensures res::lseg<y,n>*y::ll<m>;
  */
{
  if (x == NULL) 
    return y;
  node_t* s = x;
  while (x->next != NULL)
    /*@
      requires x::ll<n> & n>=1
      ensures x::lseg<x',n-1>*x'::node<_,null>;
    */
    x = x->next;
  x->next = y;
  return s;
}
void main ()
{
  int n = abs(__VERIFIER_nondet_int());
  node_t* x = new_ll(n);
  node_t* y = new_ll(n + 1);
  node_t* z = append(x, y);
  int z_length = length(z);
}




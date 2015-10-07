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

cll<n> == self::node<_,q>*q::lseg<self,n-1>
inv n>=1;

lemma_safe self::lseg<p,n> <- self::lseg<q,m>*q::node<_,p> & n=m+1.
*/

typedef struct node {
  int val;
  struct node* next;
} node_t;

node_t* new_lseg(node_t* p, int n)
  /*@
    requires n >=0
    ensures res::lseg<p,n>;
  */
{
  if (n==0)
    return p;
  node_t* x = malloc(sizeof(node_t));
  x->val = n;
  x->next = new_lseg(p, n-1);
  return x;
}

// Create a circular linked list with length n via new_lseg
node_t* new_cll(int n)
  /*@
    requires n >= 1
    ensures res::cll<n>;
  */
{
  node_t* x = malloc(sizeof(node_t));
  x->val = n;
  x->next = new_lseg(x,n-1);
  return x;
}

void traverse (node_t* _head)
  /*@
     requires _head::cll<n>
     ensures false;
  */
{
  node_t* curr = _head;
  while (curr != NULL) 
    /*@
      requires curr::cll<n>@L & Loop
      ensures false;
    */
  {
    curr = curr->next ;
  }
}

void main ()
  /*@
    requires true
    ensures false;
  */
{
  int n = abs(__VERIFIER_nondet_int());
  node_t* x = new_cll(n + 1);
  traverse(x);
}




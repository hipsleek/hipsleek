/*
 * Date: 30/09/2015
 * Created by: Ton Chanh Le (chanhle@comp.nus.edu.sg)
 */
 
#include <stdlib.h>

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

lemma_safe self::lseg<null,n> <-> self::ll<n>.

*/

typedef struct node {
    int val;
    struct node* next;
} node_t;

//Initialize a circular / null-terminating linked list with length n
node_t* init_nondet_ll (int n)
/*@
    requires n>=1
    ensures res::ll<_> or res::cll<n>;
  */
{
  node_t* head;
  node_t* curr = alloca(sizeof(node_t));
  
  curr->val = 0;
  head = curr;
  
  for (int i = 1; i < n; i++)
    /*@ 
       requires curr::node<i-1,_> & i<=n & Term[n-i]
       ensures  curr::lseg<curr',n-i>*curr'::node<n-1,_> & i'=n & i'>=i;
    */
  {
    node_t* next_node = alloca(sizeof(node_t));
    next_node->val = i;
    curr->next = next_node;
    curr = next_node;
  }
  if (__VERIFIER_nondet_int()) 
    curr->next = head;
  else 
    curr->next = NULL;
  return curr;
}

void safe_search (node_t* h, int i)
  /*@
    requires h::ll<n> or h::cll<n>
    ensures true;
  */
{
  node_t* curr = h;
  while (curr != NULL && curr->val != i) 
    /*@
      requires curr::ll<n> or curr::cll<n>
      ensures curr'::node<i,_> or curr' = null;
    */
  {
    curr = curr->next;
  }
}
void main ()
{
  int n = __VERIFIER_nondet_int();
  node_t* head = init_nondet_ll(n);
  safe_search(head, __VERIFIER_nondet_int() % n);
}




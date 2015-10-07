/*
 * Date: 30/09/2015
 * Created by: Ton Chanh Le (chanhle@comp.nus.edu.sg)
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

//Initialize a circular linked list with length n
node_t* init_cll (int n)
  /*@
    requires true
    ensures true;
  */
{
  node_t* head;
  node_t* curr = alloca(sizeof(node_t));
  
  curr->val = 0;
  head = curr;
  
  for (int i = 1; i < n; i++) 
    /*@
       requires curr::node<i-1,_>
       ensures curr'::node<x,_> & x>=n-1;
    */
  {
    node_t* next_node = alloca(sizeof(node_t));
    next_node->val = i;
    curr->next = next_node;
    curr = next_node;
  }
  
  curr->next = head;
  return head;
}

/*void search (node_t* head, int i)*/
/*{*/
/*  node_t* curr = head;*/
/*  while (curr->val != i) {*/
/*    curr = curr->next;*/
/*  }*/
/*}*/


/*void main ()*/
/*{*/
/*  int n = __VERIFIER_nondet_int();*/
/*  node_t* head = init_cll(n);*/
/*  search(head, __VERIFIER_nondet_int());*/
/*}*/




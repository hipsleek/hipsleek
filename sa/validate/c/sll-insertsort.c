#include "../../../examples/working/cparser/stdhip.h"

struct node {
	int val; 
	struct node* next;
};


/* view for a singly linked list */
/*@
ll<> == self = null
	or self::node<_, q> * q::ll<>
  inv true;
*/
/*@
HeapPred H1(node a, int v).
  HeapPred G1(node a, int v).
*/
struct node* insert(struct node* x, int v)
/*
  requires x::node<_,p> * p::ll<>
  ensures x::node<_,p1> * p1::ll<> * res::ll<>;
*/
/*@
  infer[H1,G1]
  requires H1(x, v)
     ensures G1(x, v);
*/
{
        struct node* tmp_null = NULL;
        struct node* xn;

   if (v <= x->val) {
     struct node* tmp = malloc (sizeof(struct node));
     tmp->val = v;
     tmp->next = x;
     /* return new node(v, x); */
     return tmp;
   }
   else {
     // assume false;
     if (x->next != NULL)
       {
         xn = insert(x->next, v);
         x->next = xn;
         return x;
       }
     else
       { // assume false;
         struct node* tmp = malloc (sizeof(struct node));
         tmp->val = v;
         tmp->next = NULL;
         /* x->next = new node(v, tmp_null); */
         x->next = tmp;
         return x;
       }
   }
}

#include "../../../examples/working/cparser/stdhip.h"

struct node {
  int val; 
  struct node* next; 
};
struct node* alloc()
/*@
 requires true
  ensures res::node<_,_> ;
*/
{
   return malloc(sizeof(struct node));
}

/* view for a singly linked list */
/*@
ll<v> == self = null
	or (exists v1: self::node<_, q> * q::ll<v> & v1<v)
  inv true;
*/
/*@
HeapPred H1(node a, int v).
  HeapPred G1(node a, int v).
*/
struct node* insert(struct node* x, int v)
  /* requires x::node<_,p> * p::ll<>
   ensures res::node<_,p1> * p1::ll<> ; */
/*@
  infer[H1,G1]
  requires H1(x, v)
     ensures G1(x, v);
*/
{
  struct node* xn;

   if (v <= x->val) {
     struct node* tmp = malloc(sizeof(struct node));
     tmp->val = v;
     tmp->next = x;
     return tmp;//new node(v, x);
   }
   else {
     // assume false;
     if (x->next)
       {
         xn = insert(x->next, v);
         x->next = xn;
         return x;
       }
     else
       {
         struct node* tmp = malloc(sizeof(struct node));
         tmp->val = v;
         tmp->next = NULL;
         x->next = tmp;//new node(v, tmp_null);
         return x;
       }
   }
}

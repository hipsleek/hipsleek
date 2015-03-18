struct node{
  int val;
  struct node* next;
};
#include "../examples/working/cparser/stdhip.h"

/* struct node* alloc() */
/* /\*@ */
/*  requires true */
/*   ensures res::node<_,_> ; */
/* *\/ */
/* { */
/*    return malloc(sizeof(struct node)); */
/* } */

/*@
ll<> == self = null  or self::node<_, q> * q::ll<>;

ltwo<p:node> == p=self & self = null  
   or self::node<_, q> * p::node<_,r> * q::ltwo<r>;
lthree<p:node,r:node> == p=r &r=null & self = null  
   or self::node<_, q1> * p::node<_,q2> * r::node<_,q3> * q1::lthree<q2,q3>;
*/
/*@
HeapPred H(node a, node b).
PostPred G(node a, node b, node c).
*/
struct node* zip (struct node* x, struct node* y)
//@ infer [H,G]  requires H(x,y)  ensures  G(x,y,res);
// requires x::ltwo<y>  ensures x::lthree<y,res>;
{
   if (x==NULL) 
     {
       if (y==NULL) return x;
       else 
         {
           //@ assume false;
           return x;
         }
     }
   else {
     struct node* tmp =  malloc(sizeof(struct node));//alloc();
     //@ dprint;
     tmp->val = x->val+y->val;
     tmp->next = zip(x->next,y->next);
     return tmp;//new node(x.val+y.val, zip(x.next,y.next));
   }
}

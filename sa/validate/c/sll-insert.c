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
HeapPred H1(node a).
HeapPred G1(node a,node b).
*/
struct node* alloc()
/*@
 requires true
  ensures res::node<_,_> ;
*/
{
   return malloc(sizeof(struct node));
}

struct node* insert(struct node* x, int a)
  /*requires x::node<_,p>* p::ll<> 
     ensures  x::node<_,q>* q::ll<> & res=x ;
  */
/*@
 infer[H1,G1]
  requires H1(x)
  ensures G1(x,res);
*/
{
  //dprint;
  if (!x->next){
    //struct node* tmp = malloc(sizeof(struct node));//new node(a, tmp);
    struct node* tmp = alloc();
    tmp->val =a ;
    tmp->next = NULL;
    x->next = tmp;
  }
  else 
    insert(x->next, a);
  return x;
} 

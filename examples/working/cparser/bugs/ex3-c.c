
struct node {
  int val;
  struct node* next;
};

/*@
pred_prim memLoc<heap:bool,size:int>
  inv size>0;
*/

/*@
ll<> == self=null
  or self::node^<_,p>*p::ll<>;
*/

//HeapPred H( node__star a).
//HeapPred G( node__star a).


//requires x::ll<>
// ensures  x::ll<>;

void foo(struct node* x)

//  infer [H,G]
//  requires H(x)
// ensures  G(x);

 {
   if (x != NULL) {
     foo(x->next);
     x = NULL;
   }
   return;
 }


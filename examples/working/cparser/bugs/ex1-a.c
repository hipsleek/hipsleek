
struct node {
  int val;
  struct node* next;
} _node;
/*@
ll<> == self=null
  or self::node^<_,p>*p::ll<>;

 */

// requires x::ll<>
// ensures  x::ll<>;

/*@
HeapPred H(node__star a).
HeapPred G(node__star a).
*/
void foo(struct node* x)
/*@
 infer [H,G]
 requires H(x)
 ensures  G(x);
*/
 {
   if (x) {
     foo(x->next);
   }
   return;
 }



struct node {
  int val;
  struct node* next;
};

/*@
ll<> == self=null
  or self::node<_,p>*p::ll<>;
*/

/*@
HeapPred H( node a).
HeapPred H1( node a).
*/

//requires x::ll<>
// ensures  x::ll<>;

void foo(struct node* x)
/*@
  infer [H1,H]
  requires H(x)
 ensures  H1(x);
*/
 {
   if (x != NULL) {
     foo(x->next);
   }
   return;
 }


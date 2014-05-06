
struct node {
  int val;
  struct node* next;
};

/*@
ll<> == self=null
  or self::node<_,p>*p::ll<>;
*/

/*@
HeapPred H2( node a).
HeapPred G2( node a).
*/

//requires x::ll<>
// ensures  x::ll<>;

void foo(struct node* x)
/*
  requires x::ll<>
 ensures  x::ll<>;
 */
/*@
  infer [H2,G2]
  requires H2(x)
 ensures  G2(x);
*/
 {
   if (x == NULL) return;
   else {return foo (x->next);}
 }


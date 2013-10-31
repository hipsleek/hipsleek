
struct node {
  int val;
  struct node* next;
};

/*@
ll<> == self=null
  or self::node<_,p>*p::ll<>;
*/

/*
HeapPred H( node__star a).
HeapPred G( node__star a).
*/

//requires x::ll<>
// ensures  x::ll<>;
/*
 infer [H,G]
  requires H(x)
 ensures  G(x);
*/

void foo(struct node* x)
/*@
 requires x::ll<>
 ensures  x::ll<>;
*/
 {
   if (x != 0) {
     foo(x->next);
   }
   return;
 }

void main()
{
  return;
}

/*

why List.combine error?

*/



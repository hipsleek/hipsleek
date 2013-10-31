
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
HeapPred G( node a).
HeapPred H1( node a).
HeapPred G1( node a).
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
  /*
 infer [H,G]
  requires H(x)
 ensures  G(x);
*/
 {
   if (!x) {
     return;
   }
   else
     foo(x->next);
   return;
 }

void goo(struct node* x)
/*
 requires x::ll<>
 ensures  x::ll<>;
*/
  /*@
 infer [H1,G1]
  requires H1(x)
 ensures  G1(x);
*/
 {
   if (x) {
     goo(x->next);
   }
   return;
 }

void hoo(struct node* x)
/*
 requires x::ll<>
 ensures  x::ll<>;
*/
 {
   if (x) {
     hoo(x->next);
   }
   return;
 }


void main()
/*@
 requires true
 ensures  true;
*/
{
  return;
}

/*

why List.combine error?

*/



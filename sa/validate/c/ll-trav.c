
struct node {
  int val;
  struct node* next;
};

/*
ll<> == self=null
  or self::node<_,p>*p::ll<>;
*/

/*@
HeapPred H( node a).
HeapPred H1( node a,node b).
HeapPred H2( node a).
HeapPred G2( node a).
*/

//requires x::ll<>
// ensures  x::ll<>;

void foo(struct node* x)
/*@
  infer [H2,G2]
  requires H2(x)
 ensures  G2(x);
*/
 {
   while (x)
     /*@
       infer [H1,H]
       requires H(x)
       ensures  H1(x,x');
     */
     {
     x= x->next;
   }
   return;
 }


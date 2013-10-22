
struct node {
  int val;
  struct node* next;
}
/*
H<> == self::node<_,p> * p::ll<>
  inv true;

ll<> == self=null
	or self::node<_, q> * q::ll<> & self!=null
	inv true;

lseg<p> == self=p
  or self::node<_, q> * q::lseg<p>
  inv true;


H1<> == self::node<_,p> & p=null
	or self::node<_, q> * q::H1<>
	inv true;
*/
/*@
HeapPred H(node a).
HeapPred G(node a).
*/

void foo(struct node* x)
/*@
 infer [H,G]
 requires H(x)
 ensures  G(x);
*/
 {
   if (x) {
     foo(x.next);
   }
 }

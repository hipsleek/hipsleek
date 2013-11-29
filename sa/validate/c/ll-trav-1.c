
struct node {
  int val;
  struct node* next;
};
/*@
H<> == self::node<_,p> * p::ll<>
  inv true;
*/
/*@
ll<> == self=null
	or self::node<_, q> * q::ll<> & self!=null
	inv true;

lseg<p> == self=p
  or self::node<_, q> * q::lseg<p>
  inv true;
*/
  /*@
H1<> == self::node<_,p> & p=null
	or self::node<_, q> * q::H1<>
	inv true;
*/
/*@
HeapPred H(node a).
HeapPred H1(node a).
*/

void foo(struct node* x)
/*@
 infer [H,H1]
 requires H(x)
 ensures  H1(x);
*/
/*
  requires x::H<>
  ensures x::H1<>;
*/
 {
   x = x->next;
   if (x) {
     foo(x);
   }
 }

/*
 prepost for x!=null
 requires true
 ensures res & x!=null \/ !res & x=null

 // for x.next
 infer [H,G] H(x) |- x::node<a,q>@L
  --> [H,G,H1] x::node<a,q>*H1(x,q)
   with H(x) -> x::node<a,q>*H1(x,q)

 //function call on x!=null
 [H,G,H1] x::node<a,q>*H1(x,q) |- true --* b & q!=null \/ !(b) & x=null
  -->  x::node<a,x'>*H1(x,x') &  b & q!=null
       or x::node<a,x'>*H1(x,x') &  !b & q!=null

 //state after then branch
 [H,G,H1] x::node<a,x'>*H1(x,x') &  b & x'!=null

 //recursive function call
 [H,G,H1] x::node<a,x'>*H1(x,x') &  b & x'!=null
    |- H(x') --* G(x',x")
  --> [H,G,H1] x::node<a,x0> * G(x0,x') & x0!=null
   with x'!=null & H1(x,x') -> H(x')

 //Postcondition for then branch
  [H,G,H1] x::node<a,x0> * G(x0,x') & b & x0!=null

     |- G(x,x')
  with x::node<a,x0> * G(x0,x') & x0!=null -> G(x,x')

 state after else branch
 [H,G,H1] x::node<a,x'>*H1(x,x') &  !b & x'=null

 //Postcondition for else branch
  [H,G,H1] x::node<a,x'> * H1(x,x') & b & x'=null
     |- G(x,x')
  with x::node<a,x'> * H1(x,x') & x'=null -> G(x,x')

inferred inductive predicates:
==============================
   H(x) -> x::node<a,q>*H1(x,q)
   x'!=null & H1(x,x') -> H(x')

   x::node<a,x0> * G(x0,x') & x0!=null -> G(x,x')
   x::node<a,x'> * H1(x,x') & x'=null -> G(x,x')

Drop first parameter of H1:
   H(x) -> x::node<a,q>*H1(q)
   x'!=null & H1(x') -> H(x')

   x::node<a,x0> * G(x0,x') & x0!=null -> G(x,x')
   x::node<a,x'> * H1(x') & x'=null -> G(x,x')
*/
/*
assume foo is teminated
H(x) --> x::node<val_15_522',next_15_523'> * HP_534(next_15_523',x)
HP_534(x',x) * x::node<val_15_542,x'> & x'!=null  --> H(x')
x::node<val_15_542,x_551> * G(x_551,x') & x_551!=null --> G(x,x')
HP_534(x',x) * x::node<val_15_540,x'> & x'=null & --> G(x,x')

assume x' can not reach to x
 H(x) --> x::node<_,p> * H1(p,x)
 H1(x',x) * x::node<_,x'> & x'!=null --> H(x')
 x::node<_,x0> * G(x') * HP_554(x0,x',x) & x0!=null --> G(x')
 H1(x',x) * x::node<_,x'> & x'=null --> G(x')

*/

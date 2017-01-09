data node {
  int val;
  node next;
}

HeapPred H(node a).
HeapPred H1(node a).
HeapPred ll(node a).
HeapPred G(node a, node b).
HeapPred HP_535(node a, node b).
HeapPred HP_537(node a, node b).

void foo(ref node x)
 infer [H,G]
 requires H(x)
 ensures  G(x,x'); //'
 {
   bool b;
   x = x.next;
   b = x!=null;
   if (b) {
     foo(x);
   }
 }




/*
Result-

Constrs:
========
HP_535(x',x) * x::node<val_17_543,x'>&x'!=null --> H(x')
x::node<val_17_543,x_552>@M[Orig] * G(x_552,x')&x_552!=null --> G(x,x')
H(x) --> x::node<val_17_523',next_17_524'> *  HP_535(next_17_524',x)
HP_535(x',x) * x::node<val_17_541,x'>&x'=null --> G(x,x')

DEfs:
======
HP_556(x):: 	x::node<val_17_543,x_552> * HP_556(x_552) or x::node<val_17_541,x'>&x'=null
HP_535(x')::	emp&x'=null or x'::node<val_17_523',next_17_524'> * HP_535(next_17_524')
HP_557(x')::  	emp&x'=null
H(x)::  	x::node<val_17_523',next_17_524'> * HP_535(next_17_524')
G(x,x')::  	HP_556(x) * HP_557(x')

new (3/10)
====
[HP_RELDEFN G:  G(x,x')::  
 x::node<val_19_548,x_557> * G(x_557,x')&x_557!=null
 or x::node<val_19_546,x'>&x'=null
//cmt: was not be splt -> harder to understand

*/
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
    |- H(x') --* G(x',x'')
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


(HP_535(x',x) *  @M[Orig]&x'!=null --> H(x')
 (x::node<val_16_543,x_552>@M[Orig] * G(x_552,x')&x_552!=null --> G(x,x')
 (H(x)--> x::node<val_16_523',next_16_524'> * 
 HP_535(next_16_524',x)
 HP_535(x',x) * x::node<val_16_541,x'>&x'=null --> G(x,x')

*/

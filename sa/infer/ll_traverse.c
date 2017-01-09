void foo(ref node x)
 infer [H,G]
 requires H(x)
 ensures  G(x,x');
 {
  x = x.next
  b = x!=null
  if (b) { foo(x)
  else {
  }
 }

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

Normalise? quite tricky!
========================
 H(x)  <-> x::node<_,q>*H1(q)
 H1(x) <-> x=null \/ x::node<_,q>*H1(q)
 G(x,x') <-> H(x) & x'=null


Given
    (1) H(x) -> x::node<a,q>*H1(q)
    (2) x'!=null & H1(x') -> H(x')
    (3) x::node<a,x0> * G(x0,x') & x0!=null -> G(x,x')
    (4) x::node<a,x'> * H1(x') & x'=null -> G(x,x')
        x::node<a,x'> & x'=null -> G(x,x')

    From (4):
    (5)   H1(x') -> x'=null -> emp
    From (2) & (1):
    (6) H1(x') -> x'!=null -> x'::node<_,q>*H1(q)
    Generalize (5) & (6):
     H1(x) <-> x=null & emp \/ x!=null & x::node<_,q>*H1(q)

    Let G(x,x') = K(x) * L(x')

    x::node<a,x0> * K(x0) * L(x') & x0!=null -> K(x) * L(x')
    x::node<a,x'> & x'=null -> K(x) * L(x')

    x::node<a,x0> * K(x0) & x0!=null -> K(x)
    L(x')                            -> L(x')

    x::node<a,x'> & x'=null          -> K(x)
    x'=null                          -> L(x')

    Generalize:
      L(x') <-> x'=null
      K(x) <-> x::node<a,x0> * K(x0) & x0!=null
            \/ x::node<a,x'> & x'=null

    Let K(x) <-> x::node<a,x0> * M(x0)

    Derive:
     M(x) <-> x=null & emp \/ x!=null & x::node<_,q>*M(q)

    Thus, we have:

        H(x) <-> x::node<a,q>*H1(q)
        G(x,x') <-> H(x) * x'=null
        H1(x) <-> x=null & emp \/ x!=null & x::node<_,q>*H1(q)

data node {
  int val;
  node next;
}

HeapPred H(node a).
HeapPred H1(node a).
HeapPred G(node a, node b).

 prepost for x!=null
 requires true
 ensures res & x!=null \/ !res & x=null

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

inferred inductive predicates:
==============================
   H(x) -> x::node<a,q>*H1(x,q)
   x'!=null & H1(x,x') -> H(x')

   x::node<a,x0> * G(x0,x') & x0!=null -> G(x,x')
   x::node<a,x'> * H1(x,x') & x'=null -> G(x,x')

Drop parameters
============================
H(x) -> x::node<a,q>*H1(x,q)
//RHS: x is defined (is node) -----------assume that q does not reach to x
	
 x'!=null & H1(x,x') -> H(x')
//LHS: x: is not used in RHS(x' only and no extend in LHS)

x::node<a,x0> * G(x0,x') & x0!=null -> G(x,x')
//no

x::node<a,x'> * H1(x,x') & x'=null -> G(x,x')
//x: is defined (well_defined)

Drop first parameter of H1:
   H(x) -> x::node<a,q>*H1(q)
   x'!=null & H1(x') -> H(x')

   x::node<a,x0> * G(x0,x') & x0!=null -> G(x,x')
   x::node<a,x'> * H1(x') & x'=null -> G(x,x')


Substitute:
=============================
   H(x) -> x::node<a,q>*H1(q)
   x'!=null & H1(x') -> H(x')
   x::node<a,x0> * G(x0,x') & x0!=null -> G(x,x')
   x::node<a,x'> * H1(x') & x'=null -> G(x,x')

constrain 1 + constrain 2
   H(x) -> x::node<a,q>*H1(q)
   x'!=null & H1(x') -> H(x')
   x::node<a,x0> * G(x0,x') & x0!=null -> G(x,x')
   x::node<a,x'> * H1(x') & x'=null -> G(x,x')
   x'!=null & H1(x') -> x'::node<a,q>*H1(q)

Collect partial definitions:
=============================
H(x) -> x::node<a,q>*H1(q)
//no

x'!=null & H1(x') -> H(x')
//no

x::node<a,x0> * G(x0,x') & x0!=null -> G(x,x')
//no

x::node<a,x'> * H1(x') & x'=null -> G(x,x')
//H1(x') --> x'=null --> emp
//new assume: x::node<a,x'> * emp & x'=null -> G(x,x')


x'!=null & H1(x') -> x'::node<a,q>*H1(q)
//H1(x') -> x'!=null -> x'::node<a,q>*H1(q)
//new assume: x'!=null & x'::node<a,q>*H1(q) -> H(x')

//H1(x) <-> x=null & emp \/ x!=null & x::node<a,q>*H1(q) collect when true -> x = null | x!= null

collect new assume:
H(x) -> x::node<a,q>*H1(q)
x'!=null & x'::node<a,q>*H1(q) -> H(x')
x::node<a,x0> * G(x0,x') & x0!=null -> G(x,x')
x::node<a,x'> * emp & x'=null -> G(x,x')

definitions:
H1(x) <-> x=null & emp \/ x!=null & x::node<a,q>*H1(q)

Collect that kind of definition when x::node<a,q>*H1(q) |- x'!=null & x'::node<a,q>*H1(q)
H(x) -> x::node<a,q>*H1(q)
x'!=null & x'::node<a,q>*H1(q) -> H(x')
===> H(x) <-> x::node<a,q>*H1(q)  (plus: H1 is defined)

Filter assumes:
====================
x::node<a,x0> * G(x0,x') & x0!=null -> G(x,x')
x::node<a,x'> * emp & x'=null -> G(x,x')

Split
G(x,x') = K(x) * L(x') -----> assume that x' does not reach to x

x::node<a,x0> * K(x0) * L(x') & x0!=null -> K(x) * L(x')
x::node<a,x'>  & x'=null -> K(x) * L(x')

L(x') ->  L(x')
x::node<a,x0> * K(x0) & x0!=null -> K(x) 
x::node<a,x'>  & x'=null -> K(x)
x'=null -> L(x')

//In all three constrains: RHS: hp, LHS: well-defined for hp's paras.
x'=null -> L(x')
x::node<a,x0> * K(x0) & x0!=null -> K(x) 
x::node<a,x'>  & x'=null -> K(x)

==> generalize? is it?

L(x) <-> x = null
K(x) <-> x::node<a,x0> * K(x0) & x0!=null \/ x::node<a,x'>  & x'=null 

Remove first node?

K(x) <-> x::node<a,x0> * M(x0) 
M(x0) <-> x0::node<a,x1> * M(x1) & x0!=null \/ emp & x0=null 
M is identical to H1 (check identical)

K(x) <-> x::node<a,x0> * H1(x0) 
K is identical with H
K(x) <-> H(x)
L(x) <-> x = null

G(x,x') <-> H(x) & x' = null

Finalize:
H(x) <-> x::node<a,q>*H1(q)
H1(x) <-> x=null & emp \/ x!=null & x::node<a,q>*H1(q)
G(x,x') <-> H(x) & x' = null



try 
x::node<val_17_543,x_552> * G_558(x_552)&x_552!=null --> G_558(x)
G_557(x')--> G_557(x')
x::node<val_17_541,x'>&x'=null--> G_558(x)
x'=null --> G_557(x')

!!! PARTIAL DEFINITIONS OF SUBCONSTRS: :[]
















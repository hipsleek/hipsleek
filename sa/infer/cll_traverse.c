
void foo(ref node x, ref node y)
 infer [H,G]
 requires H(x,y)
 ensures  G(x,x',y,y');
 {
  x = x.next
  b = x!=y
  if (b) { foo(x)
  else {
  }
 }

 prepost for x!=null
 requires true
 ensures res & x!=null \/ !res & x=null

 // for x.next
 infer [H,G] H(x,y) |- x::node<a,q>@L
  --> [H,G,H1] x::node<a,q>*H1(x,y,q)
   with H(x,y) -> x::node<a,q>*H1(x,y,q)

 //function call on x!=y
 [H,G,H1] x::node<a,q>*H1(x,q) |- true --* b & x!=y \/ !(b) & x=y
  -->  x::node<a,x'>*H1(x,x') &  b & x!=y
       or x::node<a,x'>*H1(x,x') &  !b & x!=y

 //state after then branch
 [H,G,H1] x::node<a,x'>*H1(x,y,x') &  b & x'!=y

 //recursive function call
 [H,G,H1] x::node<a,x'>*H1(x,y,x') &  b & x'!=y
    |- H(x',y') --* G(x',x",y',y")
  --> [H,G,H1] x::node<a,x0> * G(x0,x',y0,y') & x0!=y & y0 = y'
   with x'!=null & H1(x,y,x')& y'=y -> H(x',y')

 //Postcondition for then branch
  [H,G,H1] x::node<a,x0> * G(x0,x',y0,y') & b & x0!=y0 &y0 = y'
     |- G(x,x',y,y')
  with x::node<a,x0> * G(x0,x') & x0!=y & y' = y -> G(x,x',y,y')

 state after else branch
 [H,G,H1] x::node<a,x'>*H1(x,y,x') &  !b & x'=y

 //Postcondition for else branch
  [H,G,H1] x::node<a,x'> * H1(x,y,x') & b & x'=y &y' = y
     |- G(x,x',y,y')
  with x::node<a,x'> * H1(x,x') & x'=y &y' = y -> G(x,x',y,y')

inferred inductive predicates:
==============================
   H(x,y) -> x::node<a,q>*H1(x,y,q)

   x'!=null & H1(x,y,x')& y'=y -> H(x',y')

   x::node<a,x0> * G(x0,x',y,y) & x0!=y -> G(x,x',y,y)

   x::node<a,x'> * H1(x,x')  -> G(x,x',x',x')




Normalise========================

 H(x,y)  <-> x::node<_,q>*H1(q,y)
 H1(x,y) <-> x=y \/ x::node<_,q>*H1(q,y)
 G(x,x',y,y') <-> H(x,y) & x'=null &y = y'


void check(node x, node y){
	x = y;
	foo(x,y);
}

P(x,y) 

P(x,y) & x' = y
H(x',y)

P(x,y) & x' = y |- H(x',y)
P(x,y) & x' = y -> H(x',y)

H(x',y) * P(x,y) & x' = y |- G(x',x'',y,y')

G(x0,x',y,y') * H(x0,y) * P(x,y) & x0 = y |- R(x,x',y,y')

G(x0,x',y,y') * H(x0,y) * P(x,y) & x0 = y -> R(x,x',y,y')

Final:
P(x,y) -> y::node<_,q>*H1(q,y)
H1(x,y) <-> x=y \/ x::node<_,q>*H1(q,y)
x'=null & y = y' * P(x,y) -> R(x,x',y,y')




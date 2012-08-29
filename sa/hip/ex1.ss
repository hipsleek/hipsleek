void foo(ref node x)
 infer [H,G]
 requires H(x)
 ensures  G(x,x');//'
 {
  x = x.next
  if (x!=null)  foo(x)
 }
            /*
where H,G are separation predicates rather than
pure predicates. Using our tool, we should then
strive to infer the following:

 H(x)  <-> x::node<_,q>*H1(q)
 H1(x) <-> x=null \/ x::node<_,q>*H1(q)
 G(x,x') <-> H(x) & x'=null

 ================================

Some intermediate steps are highlighted below:

 // for x.next
 infer [H,G] H(x) |- x::node<a,b>@L
  --> [H,G,H1] x::node<a,b>*H1(x,b)
   with H(x) -> x::node<a,b>*H1(x,b)

 // for if then branch
 infer [H,G,H1] x::node<a,x'>*H1(x,x')
  |- x'!=null
  --> [H,G,H1,H2] x::node<a,x'>*H2(x,x') & x'!=null
   with H1(x,x') -> x'!=null -> H2(x,x')

 // for if else branch
 infer [H,G,H1] x::node<a,x'>*H1(x,x')
  |- x'=null
  --> [H,G,H1,H3] x::node<a,x'>*H3(x,x') & x'=null
    with H1(x,x') -> x'=null -> H3(x,x')

 // for foo(x) call
  [H,G,H1,H2] x::node<a,x'>*H2(x,x') & x'!=null
  |- H(x') *-> G(x',x")
  --> [H,G,H1,H2] x::node<a,x0> * G(x0,x') & x0!=null
   with x'!=null & H2(x,x') -> H(x')

 // for postcond at then branch
  [H,G,H1,H2] x::node<a,x0> * G(x0,x') & x0!=null
     |- G(x,x')
  with x::node<a,x0> * G(x0,x') & x0!=null -> G(x,x')
 // for postcond at else branch
  [H,G,H1,H3] x::node<a,x'>*H3(x,x') & x'=null
    with x::node<a,x'>*H3(x,x') & x'=null -> G(x,x')

The collection of constraints are:

  H(x) -> x::node<a,b>*H1(x,b)
  H1(x,x') -> x'!=null -> H2(x,x')
  H1(x,x') -> x'=null -> H3(x,x')
  x'!=null & H2(x,x') -> H(x')
  x::node<a,x0> * G(x0,x') & x0!=null -> G(x,x')
  x::node<a,x'>*H3(x,x') & x'=null -> G(x,x')

They must now be systematically simplified to the following:

 H(x)  <-> x::node<_,q>*H1(q)
 H1(x) <-> x=null \/ x::node<_,q>*H1(q)
 G(x,x') <-> H(x) & x'=null
            */

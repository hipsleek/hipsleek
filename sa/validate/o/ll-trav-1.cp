HeapPred HP_1c(node a).
HeapPred HP_1a(node a).
HeapPred HP_1b(node a).

foo:SUCCESS[
ass [H,H1][]:{
   H(x) --> x::node<_,p> * HP_1c(p);
   HP_1c(x')&x'!=null --> H(x');
   HP_1c(x') * x::node<_,x'>&x'=null --> H1(x);
   x::node<_,x'> * H1(x')&x'!=null --> H1(x)
 }

hpdefs [H,H1][]:{
  H1(x) <-> x::node<_,p> & p=null or  x::node<_,p> * H1(p) & p!=null;
  H(x) <-> x::node<_,p> * HP_1b(p);
  HP_1b(x) <-> x=null or x::node<_,p>*HP_1b(p)
 }
]

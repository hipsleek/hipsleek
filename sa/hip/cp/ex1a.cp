HeapPred HP_1(node a).
HeapPred HP_1a(node a).

foo:SUCCESS[
ass [H,H1][]:{
  H(x)&x!=null --> x::node<_,p> * HP_1a(p);
  HP_1a(x') --> H(x')&true;
  x::node<_,x'> * H1(x')&true --> H1(x)&true;
  H(x) & x=null --> emp&true;
  emp&x=null --> H1(x)&true
 }

hpdefs [H,H1][]:{
  H1(x) --> H(x);
  H(x) --> x=null or x::node<_,p>*H(p)
 }
]

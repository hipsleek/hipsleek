HeapPred HP_1(node a).
HeapPred HP_1a(node a).

foo:SUCCESS[
ass [H2,G2][]:{
  H2(x)&x!=null --> x::node<_,p> * HP_1a(p);
  HP_1a(x') --> H2(x')&true;
  x::node<_,x'> * G2(x')&true --> G2(x)&true;
  H2(x) & x=null --> G2(x)&true
 }

hpdefs [H,H1][]:{
  H2(x) <->  x=null or x::node<_,p> * H2(p);
  G2(x) <-> x=null or x::node<_,p> * G2(p)
 }
]

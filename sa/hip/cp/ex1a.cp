HeapPred HP_1(node a).
HeapPred HP_1a(node a).

foo:SUCCESS[
ass [H,H1][]:{
    H(x)&x=null --> H1(x)&true;
    x::node<_,x'> * H1(x')&true --> H1(x)&true;
    HP_1a(x') --> H(x')&true;
    H(x)&x!=null --> x::node<_,p> * HP_1a(p)
 }

hpdefs [H,H1][]:{
  H1(x) --> x=null or x::node<_,p>*H1(p);
  H(x) --> x=null or x::node<_,p>*H(p)
 }
]

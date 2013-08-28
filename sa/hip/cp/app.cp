HeapPred HP_1(node a).
HeapPred HP_1a(node a).
HeapPred HP_2(node a, node b).

append:SUCCESS[
ass [G,H,K][]:{
  H(x) --> x::node<_,a> * HP_1a(a);
  HP_1a(a)&a!=null --> H(a);
  K(y) --> K(y);
  HP_1a(a) & a=null --> emp&true;
  K(y) * x::node<_,y> --> G(x,y);
  x::node<_,b> * G(b,y)&b!=null --> G(x,y)
}

hpdefs [G,H,K][]:{
 K(y) --> htrue;
 G(x,y) --> x::node<_,p> * HP_2(p,y) * K(y);
 H(x) --> x::node<_,p>*HP_1(p);
 HP_1(x) --> x=null or x::node<_,p1> * HP_1(p1);
 HP_2(x,p) --> p=x or x::node<_,p1> * HP_2(p1,p)
 }
]


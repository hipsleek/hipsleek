HeapPred HP_1(node a).
HeapPred HP_1a(node a).
HeapPred HP_2(node a, node b).

append:SUCCESS[
ass [H1,G2,H1a][]:{
  H1(x) --> x::node<_,a> * HP_1a(a);
  HP_1a(a)&a!=null --> H1(a);
  H1a(y) --> H1a(y);
  HP_1a(a) & a=null --> emp&true;
  H1a(y) * x::node<_,y> --> G2(x,y);
  x::node<_,b> * G2(b,y)&b!=null --> G2(x,y)
}

hpdefs [G2,H1][]:{
 H1a(y) --> htrue;
 G2(x,y) --> x::node<_,p> * HP_2(p,y) * H1a(y);
 H1(x) --> x::node<_,p>*HP_1(p);
 HP_1(x) --> x=null or x::node<_,p1> * HP_1(p1);
 HP_2(x,p) --> p=x or x::node<_,p1> * HP_2(p1,p)
 }
]


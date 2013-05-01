HeapPred HP_1(node a).
HeapPred HP_580(node a).
HeapPred HP_2(node a, node b).

append:SUCCESS[
ass [H1,G2][]:{
  H1(x) --> x::node<_,p> * HP_580(p);
  HP_580(a)&a!=null --> H1(a);
  HP_580(a) & a=null  --> emp&true;
  x::node<_,y> & y=null --> G2(x,y);
  x::node<_,b> * G2(b,y)&b!=null & y=null --> G2(x,y)
}

hpdefs [H1,G2][]:{H1(x) --> x::node<_,p>*HP_1(p);
   HP_1(x) --> x=null or x::node<_,p1> * HP_1(p1);
   G2(x,y) --> x::node<_,p> * HP_2(p,y) & y=null;
   HP_2(x,y) --> x=y or x::node<_,p1> * HP_2(p1,y)
 }
]


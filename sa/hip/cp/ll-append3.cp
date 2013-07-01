HeapPred HP_1(node a).
HeapPred HP_2(node a, node b).
HeapPred HP_617(node a).

append:SUCCESS[
ass [H1,G1][]:{
  H1(x) --> x::node<_,b> * HP_617(b);
  HP_617(b)&b!=null --> H1(b);
  HP_617(a) & a=null --> emp& true;
  x::node<_,y> --> G1(x,y);
  x::node<_,b> * G1(b,y) & b!=null --> G1(x,y)
}

hpdefs [H1,G1][]:{H1(x) --> x::node<_,p>*HP_1(p);
   H1(x) --> x::node<_,p>*HP_1(p);
   HP_1(x) --> x=null or x::node<_,p1> * HP_1(p1);
   G1(x,y) --> x::node<_,p> * HP_2(p,y);
   HP_2(x,p) --> x=p or x::node<_,p1> * HP_2(p1,p)
 }
]

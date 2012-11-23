HeapPred HP_1a(node a).

create_list:SUCCESS[
ass [G1][]:{
  G1(x) * p::node<_,x>&  true --> G1(p);
  emp&x=null --> G1(x)
 }

hpdefs [G1][]:{
         G1(x) --> x=null or x::node<_,p> * G1(p)
 }
]

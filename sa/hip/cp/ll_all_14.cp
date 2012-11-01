HeapPred HP_2(node a, node b).

create_list[
ass [G1]:{
  G1(x) * p::node<_,x>&  true --> G1(p) * HP_2(x,p);
  emp&x=null --> G1(x)
 }

hpdefs [G1]:{
         G1(x) --> x=null or x::node<_,p> * G1(p)
 }
]

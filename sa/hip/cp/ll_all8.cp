HeapPred HP_1(node a).
HeapPred HP_1a(node b).

set_null2:SUCCESS[
ass [H1,G1][]:{
     x::node<_,p1>&p1=null --> G1(x);
    H1(x) --> x::node<_,p2> * HP_1a(p2)
	}

hpdefs [G1,H1][]:{
  H1(x) --> x::node<_,q>;
  G1(x) --> x::node<_,p2> & p2 =null
 }
]

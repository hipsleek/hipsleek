HeapPred HP_1(node a).
HeapPred HP_2(node a, node b).

set_null2[
ass [H1,G1]:{
    HP_2(p,x) * x::node<_,p1>&p1=null --> G1(x) * HP_1(p);
    H1(x) --> x::node<_,p2> * HP_2(p2,x)
	}

hpdefs [G1,H1]:{
  H1(x) --> x::node<_,q>;
  G1(x) --> x::node<_,p2> & p2 =null
 }
]

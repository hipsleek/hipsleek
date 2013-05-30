        HeapPred HP_1(node a).
HeapPred HP_2a(node b, node c).

set_next:SUCCESS[
ass [H2,G2][]:{
    HP_2a(next_49_563,y) * x::node<_,y> --> G2(x,y);
    H2(x,y) --> x::node<_,next_49_548'> * HP_2a(next_49_548',y)

	}

hpdefs [G2,H2][q1]:{
 H2(x,y) --> x::node<_,q2> & q1=y;
 G2(x,y) --> x::node<_,y> & q1=y
 }
]

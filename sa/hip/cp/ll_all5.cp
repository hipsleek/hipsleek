HeapPred HP_1(node a).
HeapPred HP_2a(node a, node b).
HeapPred HP_3(node a, node b, node c).

set_next[
ass [H2,G2]:{
    HP_3(next_49_563,x,y) * x::node<val_49_564,y> -->
         G2(x,y) * HP_1(next_49_563);
    H2(x,y) --> x::node<val_49_547',next_49_548'> * HP_3(next_49_548',x,y)

	}

hpdefs [G2,H2]:{
 HP_2a(x,y) --> htrue&true;
 H2(x,y) --> x::node<_,q> * HP_2a(q,y);
 G2(x,y) --> x::node<_,y> * HP_2a(q,y)
 }
]

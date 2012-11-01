HeapPred HP_2(node a, node b).

get_next[
ass [H1,G2]:{
     HP_2(p,x) * x::node<_,p> --> G2(x,p);
     H1(x) --> x::node<_, p1> * HP_2(p1,x)
	}

hpdefs [G2,H1]:{
  H1(x) --> x::node<_,q>;
  G2(x,y) --> x::node<_,y> & y=q
 }
]

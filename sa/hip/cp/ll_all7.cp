HeapPred HP_1a( node b).

get_next:SUCCESS[
ass [H1,G2][]:{
     HP_1a(p) * x::node<_,p> --> G2(x,p);
     H1(x) --> x::node<_, p1> * HP_1a(p1)
	}

hpdefs [G2,H1][]:{
  H1(x) --> x::node<_,q>;
  G2(x,y) --> x::node<_,y> & y=q
 }
]

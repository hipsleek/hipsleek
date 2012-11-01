HeapPred HP_1(node a).
HeapPred HP_2(node a, node b).

front[
ass [F,G]:{
    HP_2(p,x) * x::node<v_int,p> --> G(x,v_int);
    F(x) --> x::node<_,p> *HP_2(p,x)

	}

hpdefs [F,G]:{
 HP_1(p) --> htrue&true;
 F(x)    --> x::node<_,n> * HP_1(n);
 G(x,res) --> x::node<res,n> * HP_1(n)

 }
]

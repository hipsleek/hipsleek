HeapPred HP_1(node a).
HeapPred HP_2(node a, node b).

front[
ass [F]:{
         F(x)&true --> x::node<val_13_519',next_13_520'> *
          HP_2(next_13_520',x)&true
	}

hpdefs [F]:{
 HP_1(p) --> htrue&true;
 F(x_537) --> x_537::node<_,p> * HP_1(p)

 }
]

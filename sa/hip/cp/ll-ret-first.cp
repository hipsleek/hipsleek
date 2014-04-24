HeapPred HP_1(node a).
HeapPred HP_1a(node a).

front:SUCCESS[
ass [F][]:{
         F(x)&true --> x::node<val_13_519',next_13_520'> *  HP_1a(next_13_520')&true
	}

hpdefs [F][]:{
 F(x_537) --> x_537::node<_,unk_HP_1>

 }
]

/*
hpdefs [F]:{
 HP_1(p) --> htrue&true;
 F(x_537) --> x_537::node<_,p> * HP_1(p)

 }
*/

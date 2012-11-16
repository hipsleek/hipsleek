HeapPred HP_1(node a).
HeapPred HP_2(node a, node b).

ret_first:SUCCESS[
ass [H1,G2][]:{
    H1(x) & v=x --> G2(x,v)
	}

hpdefs [H1,G2][]:{
 H1(x) --> emp&x=H1_x_540;
 G2(x,y) --> x=y

 }
]

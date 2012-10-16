HeapPred HP_1(node a,node b).
HeapPred HP_2(node a, node b).

append[
ass [H1,H2]:{  	HP1(a,x) * x::node<_,y>&a=null -> G2(x,y),
		H2(x,y) -> x::node<_,b> * HP1(b,x),
		HP1(a,x)&a!=null -> H2(a,y),
		x::node<_,b> * G2(b,y)&b!=null -> G2(x,y)	}

hpdefs [G2,H2]:{
 G2(x,y) -> x::node<_,p> * HP_2(p,y),
 H2(x,y) -> x::node<_,p>*HP_1(p,y),
 HP_1(x,y) -> x=null or x::node<_,p1> * HP_1(p1,y),
 HP_2(x,p) -> x=p or x::node<_,p1> * HP_2(p1,p)
 }
]


/*
HP_RELDEFN HP_619:  HP_619(y_618,y)::  
 emp&y_618=y
 or y_618::node<val_57_617,y_622> * HP_619(y_622,y)&y_618!=null

HP_RELDEFN HP_619:  HP_619(y_618,y)::  
 emp&y_618=y
 or y_618::node<val_59_617,y_622> * HP_619(y_622,y)&y_618!=null

*/


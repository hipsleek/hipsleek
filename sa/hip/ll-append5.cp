HeapPred HP_615(node a, node b).
HeapPred HP_618(node a, node b).
HeapPred HP_619(node a, node b).
HeapPred HP_618(node a, node b).

append[
ass [H1,H2]:{  	HP1(a,x) * x::node<_,y>&a=null -> G2(x,y),
		H2(x,y) -> x::node<_,b> * HP1(b,x),
		HP1(a,x)&a!=null -> H2(a,y),
		x::node<_,b> * G2(b,y)&b!=null -> G2(x,y)	}

hpdefs [H2,G2]:{ 
G2(x,y) -> x::node<val_55_609,y_610> * HP_619(y_610,y)&true,
H2(x,y) ->  x::node<val_55_616,next_55_617> * HP_618(next_55_617,y)&true,
HP_619(y_618,y)->  
 emp&y_618=y
 or y_618::node<val_59_617,y_622> * HP_619(y_622,y)&y_618!=null

 ,
HP_618(next_55_617,y) -> 
 emp&next_55_617=null
 or next_55_617::node<val_55_616,next_55_621> * HP_618(next_55_621,y)&true

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


HeapPred HP_1(node a,node b).
HeapPred HP_2(node a, node b).
HeapPred HP_579(node a,node b).
HeapPred HP_611(node a, node b).
HeapPred HP_618(node a,node b).


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
append[
ass [H2,G2]: {
 HP_579(v_node_56_596,x) * x::node<val_56_585,y>&v_node_56_596=null ->  G2(x,y)&true,
 H2(x,y)&true ->  x::node<val_56_560',next_56_561'> * HP_579(next_56_561',x)&true,
 HP_579(v_node_56_602,x)&v_node_56_602!=null ->  H2(v_node_56_602,y)&true,
 x::node<val_56_587,v_node_56_602> * G2(v_node_56_602,y)&v_node_56_602!=null ->  G2(x,y)&true
}
hpdefs [H2,G2]: {
 HP_579(v_node_56_596)&true ->  
 v_node_56_596::node<val_56_616,next_56_617> * HP_618(next_56_617,y)&true
 or v_node_56_596::node<val_56_560',next_56_561'> * 
    next_56_561'::node<val_56_616,next_56_617> * HP_618(next_56_617,y)&true
 or emp&v_node_56_596=null
 ,
 G2(x,y)&true ->  x::node<val_56_609,y_610> * HP_611(y_610,y)&true,
 H2(x,y)&true ->  x::node<val_56_616,next_56_617> * HP_618(next_56_617,y)&true,
 HP_611(y_610,y)&true ->  
 emp&y_610=y
 or y_610::node<val_56_609,y_614> * HP_611(y_614,y)&true
 ,
 HP_618(next_56_617,y)&true ->  
 emp&next_56_617=null
 or next_56_617::node<val_56_616,next_56_621> * HP_618(next_56_621,y)&true
 
}
]
*/

/*
HP_RELDEFN HP_619:  HP_619(y_618,y)::  
 emp&y_618=y
 or y_618::node<val_57_617,y_622> * HP_619(y_622,y)&y_618!=null

HP_RELDEFN HP_619:  HP_619(y_618,y)::  
 emp&y_618=y
 or y_618::node<val_59_617,y_622> * HP_619(y_622,y)&y_618!=null

*/


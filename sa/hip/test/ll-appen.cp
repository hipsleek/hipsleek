HeapPred HP_618(node next_56_617, node y).
HeapPred HP_611(node y_610, node y).
HeapPred HP_579(node next_56_561', node x').
HeapPred HP1(node a, node b).
HeapPred H2(node a, node b).
HeapPred H1(node a).
HeapPred G3(node b, node c, node d).
HeapPred G2(node a, node b).
HeapPred G1(node a).

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


HeapPred HP_619(node next_32_618).
HeapPred HP_612(node y_611, node y).
HeapPred HP_580(node next_32_562', node x').
HeapPred HP1(node a, node b).
HeapPred H2(node a, node b).
HeapPred H1(node a).
HeapPred G3(node b, node c, node d).
HeapPred G1(node a).
HeapPred G2(node a, node b).

append[
ass [H1,G2]: {
 HP_580(v_node_32_597,x) * x::node<val_32_586,y>&y=null & v_node_32_597=null -->  G2(x,y)&true;
 H1(x)&true -->  x::node<val_32_561',next_32_562'> * HP_580(next_32_562',x)&true;
 HP_580(v_node_32_603,x)&v_node_32_603!=null -->  H1(v_node_32_603)&true;
 x::node<val_32_588,v_node_32_603> * G2(v_node_32_603,y)&y=null & 
v_node_32_603!=null -->  G2(x,y)&true
}
hpdefs [H1,G2]: {
 HP_580(v_node_32_597)&true -->  
 v_node_32_597::node<val_32_617,next_32_618> * HP_619(next_32_618)&true
 or v_node_32_597::node<val_32_561',next_32_562'> * 
    next_32_562'::node<val_32_617,next_32_618> * HP_619(next_32_618)&true
 or emp&v_node_32_597=null
 ;
 G2(x,y)&true -->  x::node<val_32_610,y_611> * HP_612(y_611,y)&true;
 H1(x)&true -->  x::node<val_32_617,next_32_618> * HP_619(next_32_618)&true;
 HP_612(y_611,y)&true -->  
 emp&y_611=y & y=null
 or y_611::node<val_32_610,y_615> * HP_612(y_615,y)&y=null
 ;
 HP_619(next_32_618)&true -->  
 emp&next_32_618=null
 or next_32_618::node<val_32_617,next_32_622> * HP_619(next_32_622)&true
 
}
]


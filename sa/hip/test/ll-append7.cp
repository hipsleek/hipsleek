HeapPred HP_616(node next_32_562').
HeapPred HP_611(node y_610, node y).
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
 HP_616(next_32_562')&true
 or emp&v_node_32_597=null
 ;
 HP_611(y_610,y)&true -->  
 emp&y_610=y
 or y_610::node<val_32_586,y_614> * HP_611(y_614,y)&true
 ;
 HP_616(next_32_562')&true -->  
 emp&next_32_562'=null
 or next_32_562'::node<val_32_561',next_32_619> * HP_616(next_32_619)&true
 ;
 G2(x,y)&true -->  x::node<val_32_586,y_610> * HP_611(y_610,y)&y=null;
 H1(x)&true -->  x::node<val_32_561',next_32_562'> * HP_616(next_32_562')&true
}
]


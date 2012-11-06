HeapPred HP_621(node next_32_562').
HeapPred HP_615(node y_613_614, node y_613).
HeapPred HP_626(node v_node_32_603).
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
 HP_626(v_node_32_611)&true -->  
 emp&v_node_32_611=null
 or HP_621(next_32_562')&true
 ;
 HP_615(y_613_614,y_613)&true -->  
 y_613_614::node<val_32_586,y_613_618> * HP_615(y_613_618,y_613)&true
 or emp&y_613_614=y_613
 ;
 HP_621(next_32_562')&true -->  
 next_32_562'::node<val_32_561',next_32_624> * HP_621(next_32_624)&true
 or emp&next_32_562'=null
 ;
 G2(x_612,y_613)&true -->  x_612::node<val_32_586,y_613_614> * HP_615(y_613_614,y_613)&y_613=null;
 H1(x_620)&true -->  x_620::node<val_32_561',next_32_562'> * HP_621(next_32_562')&true
}
]


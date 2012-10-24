HeapPred HP_615(node next_56_561', node y).
HeapPred HP_610(node y_609, node y).
HeapPred HP_579(node next_56_561', node x').
HeapPred HP1(node a, node b).
HeapPred H2(node a, node b).
HeapPred H1(node a).
HeapPred G3(node b, node c, node d).
HeapPred G2(node a, node b).
HeapPred G1(node a).

append[
ass [H2,G2]: {
 HP_579(v_node_56_596,x) * x::node<val_56_585,y>&v_node_56_596=null -->  G2(x,y)&true;
 H2(x,y)&true -->  x::node<val_56_560',next_56_561'> * HP_579(next_56_561',x)&true;
 HP_579(v_node_56_602,x)&v_node_56_602!=null -->  H2(v_node_56_602,y)&true;
 x::node<val_56_587,v_node_56_602> * G2(v_node_56_602,y)&v_node_56_602!=null -->  G2(x,y)&true
}
hpdefs [H2,G2]: {
 HP_579(v_node_56_596)&true -->  
 v_node_56_596::node<val_56_560',next_56_561'> * HP_615(next_56_561',y)&true
 or emp&v_node_56_596=null
 ;
 G2(x,y)&true -->  x::node<val_56_585,y_609> * HP_610(y_609,y)&true;
 H2(x,y)&true -->  x::node<val_56_560',next_56_561'> * HP_615(next_56_561',y)&true;
 HP_610(y_609,y)&true -->  
 emp&y_609=y
 or y_609::node<val_56_585,y_613> * HP_610(y_613,y)&true
 ;
 HP_615(next_56_561',y)&true -->  
 emp&next_56_561'=null
 or next_56_561'::node<val_56_560',next_56_618> * HP_615(next_56_618,y)&true
 
}
]


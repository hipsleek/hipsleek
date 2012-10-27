HeapPred HP_617(node next_56_561', node y).
HeapPred HP_612(node y_611, node y).
HeapPred HP_610(node y).
HeapPred HP_609(node y).
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
 emp&v_node_56_596=null
 or HP_610(y) * HP_617(next_56_561',y)&true
 ;
 HP_612(y_611,y)&true -->  
 emp&y_611=y
 or y_611::node<val_56_585,y_615> * HP_612(y_615,y)&true
 ;
 HP_617(next_56_561',y)&true -->  
 emp&next_56_561'=null
 or next_56_561'::node<val_56_560',next_56_620> * HP_617(next_56_620,y)&true
 ;
 HP_610(y)&true -->  htrue&true;
 HP_609(y)&true -->  htrue&true;
 G2(x,y)&true -->  x::node<val_56_585,y_611> * HP_612(y_611,y) * HP_609(y)&true;
 H2(x,y)&true -->  x::node<val_56_560',next_56_561'> * HP_617(next_56_561',y) * HP_610(y)&true
}
]


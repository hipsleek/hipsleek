HeapPred HP_628(node next_56_561', node y_627).
HeapPred HP_621(node y_619_620, node y_619).
HeapPred HP_609(node y).
HeapPred HP_579(node next_56_561', node y).
HeapPred HP1(node a, node b).
HeapPred H2(node a, node b).
HeapPred H1(node a).
HeapPred G3(node b, node c, node d).
HeapPred G2(node a, node b).
HeapPred G1(node a).

append:SUCCESS[
ass [H2,G2][]: {
 HP_579(v_node_56_596,y) * x::node<val_56_585,y>&v_node_56_596=null -->  G2(x,y)&true;
 H2(x,y)&true -->  x::node<val_56_560',next_56_561'> * HP_579(next_56_561',y)&true;
 HP_579(v_node_56_602,y)&v_node_56_602!=null -->  H2(v_node_56_602,y)&true;
 x::node<val_56_587,v_node_56_602> * G2(v_node_56_602,y)&v_node_56_602!=null -->  G2(x,y)&true
}
hpdefs [H2,G2][]: {
 HP_579(v_node_56_633,y_634)&true -->  
 HP_628(next_56_561',y_634)&y_634=HP_609_y_635
 or emp&v_node_56_633=null & y_634=HP_609_y_635
 ;
 HP_621(y_619_620,y_619)&true -->  
 emp&y_619_620=y_619
 or y_619_620::node<val_56_585,y_619_624> * HP_621(y_619_624,y_619)&true
 ;
 HP_628(next_56_561',y_627)&true -->  
 emp&next_56_561'=null
 or next_56_561'::node<val_56_560',next_56_631> * HP_628(next_56_631,y_627)&
    true
 ;
 HP_609(y)&true -->  htrue&true;
 G2(x_618,y_619)&true -->  x_618::node<val_56_585,y_619_620> * HP_621(y_619_620,y_619)&
y_619=HP_609_y_635;
 H2(x_626,y_627)&true -->  x_626::node<val_56_560',next_56_561'> * HP_628(next_56_561',y_627)&
y_627=HP_609_y_635
}
]


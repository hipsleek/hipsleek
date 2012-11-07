HeapPred HP_627(node next_56_561', node y_626).
HeapPred HP_620(node y_618_619, node y_618).
HeapPred HP_609(node y).
HeapPred HP_579(node next_56_561', node y).
HeapPred HP1(node a, node b).
HeapPred H2(node a, node b).
HeapPred H1(node a).
HeapPred G3(node b, node c, node d).
HeapPred G2(node a, node b).
HeapPred G1(node a).

append[
ass [H2,G2]: {
 HP_579(v_node_56_596,y) * x::node<val_56_585,y>&v_node_56_596=null -->  G2(x,y)&true;
 H2(x,y)&true -->  x::node<val_56_560',next_56_561'> * HP_579(next_56_561',y)&true;
 HP_579(v_node_56_602,y)&v_node_56_602!=null -->  H2(v_node_56_602,y)&true;
 x::node<val_56_587,v_node_56_602> * G2(v_node_56_602,y)&v_node_56_602!=null -->  G2(x,y)&true
}
hpdefs [H2,G2]: {
 HP_579(v_node_56_615,y_616)&true -->  
 HP_627(next_56_561',y_616)&y_616=HP_609_y_632
 or emp&v_node_56_615=null & y_616=HP_609_y_632
 ;
 HP_620(y_618_619,y_618)&true -->  
 emp&y_618_619=y_618
 or y_618_619::node<val_56_585,y_618_623> * HP_620(y_618_623,y_618)&true
 ;
 HP_627(next_56_561',y_626)&true -->  
 emp&next_56_561'=null
 or next_56_561'::node<val_56_560',next_56_630> * HP_627(next_56_630,y_626)&
    true
 ;
 HP_609(y)&true -->  htrue&true;
 G2(x_617,y_618)&true -->  x_617::node<val_56_585,y_618_619> * HP_620(y_618_619,y_618)&
y_618=HP_609_y_632;
 H2(x_625,y_626)&true -->  x_625::node<val_56_560',next_56_561'> * HP_627(next_56_561',y_626)&
y_626=HP_609_y_632
}
]


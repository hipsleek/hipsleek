HeapPred HP_623(node next_82_550').
HeapPred HP_617(node y_615_616, node y_615).
HeapPred HP_628(node v_node_82_596).
HeapPred HP_573(node next_82_550', node x').
HeapPred T2(node a, node b).
HeapPred T1(node a).
HeapPred HP_641(node a, node b).
HeapPred HP_648(node a).
HeapPred HP1(node a, node b).
HeapPred H2(node a).
HeapPred H1(node a).
HeapPred G3(node b, node c, node d).
HeapPred G1(node a, node b).
HeapPred G2(node a, node b).
HeapPred H(node a).

append[
ass [H1,G1]: {
 HP_573(v_node_82_590,x) * x::node<val_82_579,y>&v_node_82_590=null -->  G1(x,y)&true;
 H1(x)&true -->  x::node<val_82_549',next_82_550'> * HP_573(next_82_550',x)&true;
 HP_573(v_node_82_596,x)&v_node_82_596!=null -->  H1(v_node_82_596)&true;
 x::node<val_82_581,v_node_82_596> * G1(v_node_82_596,y)&
v_node_82_596!=null & y!=null -->  G1(x,y)&true
}
hpdefs [H1,G1]: {
 HP_628(v_node_82_613)&true -->  
 emp&v_node_82_613=null
 or HP_623(next_82_550')&true
 ;
 HP_617(y_615_616,y_615)&true -->  
 y_615_616::node<val_82_579,y_615_620> * HP_617(y_615_620,y_615)&y_615!=null
 or emp&y_615_616=y_615
 ;
 HP_623(next_82_550')&true -->  
 next_82_550'::node<val_82_549',next_82_626> * HP_623(next_82_626)&true
 or emp&next_82_550'=null
 ;
 G1(x_614,y_615)&true -->  x_614::node<val_82_579,y_615_616> * HP_617(y_615_616,y_615)&true;
 H1(x_622)&true -->  x_622::node<val_82_549',next_82_550'> * HP_623(next_82_550')&true
}
]


HeapPred HP_618(node next_82_550').
HeapPred HP_613(node y_612, node y).
HeapPred HP_623(node v_node_82_596).
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
 HP_623(v_node_82_590)&true -->  
 HP_618(next_82_550')&true
 or emp&v_node_82_590=null
 ;
 HP_613(y_612,y)&true -->  
 emp&y_612=y
 or y_612::node<val_82_579,y_616> * HP_613(y_616,y)&y!=null
 ;
 HP_618(next_82_550')&true -->  
 emp&next_82_550'=null
 or next_82_550'::node<val_82_549',next_82_621> * HP_618(next_82_621)&true
 ;
 G1(x,y)&true -->  x::node<val_82_579,y_612> * HP_613(y_612,y)&true;
 H1(x)&true -->  x::node<val_82_549',next_82_550'> * HP_618(next_82_550')&true
}
]


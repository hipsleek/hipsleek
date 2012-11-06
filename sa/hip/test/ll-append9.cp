HeapPred HP_591(node next_43_532').
HeapPred HP_585(node y_583_584, node y_583).
HeapPred HP_597(node v_node_43_573).
HeapPred HP_550(node next_43_532', node x').
HeapPred HP1(node a, node b).
HeapPred H2(node a, node b).
HeapPred H1a(node a).
HeapPred H1(node a).
HeapPred G3(node b, node c, node d).
HeapPred G1(node a).
HeapPred G2(node a, node b).

append[
ass [H1,H1a,G2]: {
 H1a(y) * HP_550(v_node_43_567,x) * x::node<val_43_556,y>&v_node_43_567=null -->  G2(x,y) * H1a(y)&true;
 emp&true -->  H1a(y)&true;
 H1(x)&true -->  x::node<val_43_531',next_43_532'> * HP_550(next_43_532',x)&true;
 HP_550(v_node_43_573,x)&v_node_43_573!=null -->  H1(v_node_43_573)&true;
 H1a(y)&true -->  H1a(y)&true;
 x::node<val_43_558,v_node_43_573> * G2(v_node_43_573,y) * H1a(y)&
v_node_43_573!=null -->  G2(x,y) * H1a(y)&true;
 emp&true -->  H1a(y)&true
}
hpdefs [H1,H1a,G2]: {
 HP_597(v_node_43_581)&true -->  
 emp&v_node_43_581=null
 or HP_591(next_43_532')&true
 ;
 HP_585(y_583_584,y_583)&true -->  
 y_583_584::node<val_43_556,y_583_588> * HP_585(y_583_588,y_583)&true
 or emp&y_583_584=y_583
 ;
 HP_591(next_43_532')&true -->  
 next_43_532'::node<val_43_531',next_43_594> * HP_591(next_43_594)&true
 or emp&next_43_532'=null
 ;
 G2(x_582,y_583)&true -->  x_582::node<val_43_556,y_583_584> * HP_585(y_583_584,y_583)&true;
 H1(x_590)&true -->  x_590::node<val_43_531',next_43_532'> * HP_591(next_43_532')&true;
 H1a(y)&true -->  htrue&true
}
]


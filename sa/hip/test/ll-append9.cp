HeapPred HP_586(node next_43_532').
HeapPred HP_581(node y_580, node y).
HeapPred HP_591(node v_node_43_573).
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
 HP_591(v_node_43_567)&true -->  
 HP_586(next_43_532')&true
 or emp&v_node_43_567=null
 ;
 HP_581(y_580,y)&true -->  
 emp&y_580=y
 or y_580::node<val_43_556,y_584> * HP_581(y_584,y)&true
 ;
 HP_586(next_43_532')&true -->  
 emp&next_43_532'=null
 or next_43_532'::node<val_43_531',next_43_589> * HP_586(next_43_589)&true
 ;
 G2(x,y)&true -->  x::node<val_43_556,y_580> * HP_581(y_580,y)&true;
 H1(x)&true -->  x::node<val_43_531',next_43_532'> * HP_586(next_43_532')&true;
 H1a(y)&true -->  htrue&true
}
]


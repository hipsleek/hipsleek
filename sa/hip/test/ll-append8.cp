HeapPred HP_587(node next_51_533').
HeapPred HP_582(node y_581, node y).
HeapPred HP_592(node v_node_51_574).
HeapPred HP_551(node next_51_533', node x').
HeapPred HP1(node a, node b).
HeapPred H2(node a, node b).
HeapPred H1b(node a).
HeapPred H1a(node a).
HeapPred H1(node a).
HeapPred G3(node b, node c, node d).
HeapPred G1(node a).
HeapPred G2(node a, node b).

append[
ass [H1,H1a,G2]: {
 H1a(y) * HP_551(v_node_51_568,x) * x::node<val_51_557,y>&v_node_51_568=null -->  G2(x,y)&true;
 H1(x)&true -->  x::node<val_51_532',next_51_533'> * HP_551(next_51_533',x)&true;
 HP_551(v_node_51_574,x)&v_node_51_574!=null -->  H1(v_node_51_574)&true;
 H1a(y)&true -->  H1a(y)&true;
 x::node<val_51_559,v_node_51_574> * G2(v_node_51_574,y)&v_node_51_574!=null -->  G2(x,y)&true
}
hpdefs [H1,H1a,G2]: {
 HP_592(v_node_51_568)&true -->  
 HP_587(next_51_533')&true
 or emp&v_node_51_568=null
 ;
 HP_582(y_581,y)&true -->  
 emp&y_581=y
 or y_581::node<val_51_557,y_585> * HP_582(y_585,y)&true
 ;
 HP_587(next_51_533')&true -->  
 emp&next_51_533'=null
 or next_51_533'::node<val_51_532',next_51_590> * HP_587(next_51_590)&true
 ;
 G2(x,y)&true -->  x::node<val_51_557,y_581> * HP_582(y_581,y) * H1a(y)&true;
 H1(x)&true -->  x::node<val_51_532',next_51_533'> * HP_587(next_51_533')&true;
 H1a(y)&true -->  htrue&true
}
]


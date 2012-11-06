HeapPred HP_592(node next_51_533').
HeapPred HP_586(node y_584_585, node y_584).
HeapPred HP_598(node v_node_51_574).
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
 HP_598(v_node_51_582)&true -->  
 emp&v_node_51_582=null
 or HP_592(next_51_533')&true
 ;
 HP_586(y_584_585,y_584)&true -->  
 y_584_585::node<val_51_557,y_584_589> * HP_586(y_584_589,y_584)&true
 or emp&y_584_585=y_584
 ;
 HP_592(next_51_533')&true -->  
 next_51_533'::node<val_51_532',next_51_595> * HP_592(next_51_595)&true
 or emp&next_51_533'=null
 ;
 G2(x_583,y_584)&true -->  x_583::node<val_51_557,y_584_585> * HP_586(y_584_585,y_584)&y_584=H1a_y_597;
 H1(x_591)&true -->  x_591::node<val_51_532',next_51_533'> * HP_592(next_51_533')&true;
 H1a(y)&true -->  htrue&true
}
]


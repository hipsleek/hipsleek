HeapPred HP_578(node next_44_544').
HeapPred HP_572(node v_node_46_548').
HeapPred HP_571(node x').
HeapPred HP_559(node next_44_544').
HeapPred HP_557(node a, node b).
HeapPred HP_537(node a, node b).
HeapPred HP_535(node a, node b).
HeapPred G4(node a, node b, node c, node d).
HeapPred G3(node a, node b, node c).
HeapPred HP_535(node a, node b).
HeapPred G2(node a, node b).
HeapPred G1(node a, node b).
HeapPred G(node a, node b).
HeapPred H2(node a).
HeapPred H1(node a).
HeapPred H(node a).

get_next:SUCCESS[
ass [H,G][]: {
 H(x)&true -->  x::node<val_44_543',next_44_544'> * HP_559(next_44_544')&true;
 HP_559(v_node_46_548') * x'::node<val_44_568,next_45_547'>&next_45_547'=null -->  G(x',v_node_46_548')&true
}
hpdefs [H,G][]: {
 HP_578(next_44_544')&true -->  HP_572(next_44_544')&true;
 HP_559(v_node_46_548')&true -->  HP_572(v_node_46_548')&true;
 HP_571(x_583)&true -->  x_583::node<val_44_568,next_45_547'>&next_45_547'=null;
 H(x_577)&true -->  x_577::node<val_44_543',next_44_544'> * HP_572(next_44_544')&true
}
]


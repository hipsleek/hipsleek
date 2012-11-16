HeapPred HP_603(node next_43_532').
HeapPred HP_597(node y_595_596, node y_595).
HeapPred HP_550(node next_43_532').
HeapPred HP1(node a, node b).
HeapPred H2(node a, node b).
HeapPred H1a(node a).
HeapPred H1(node a).
HeapPred G3(node b, node c, node d).
HeapPred G1(node a).
HeapPred G2(node a, node b).

append:SUCCESS[
ass [H1,H1a,G2][]: {
 H1a(y) * HP_550(v_node_43_567) * x::node<val_43_556,y>&v_node_43_567=null -->  G2(x,y) * H1a(y)&true;
 emp&v_node_43_567=null -->  H1a(y)&true;
 H1(x)&true -->  x::node<val_43_531',next_43_532'> * HP_550(next_43_532')&true;
 HP_550(v_node_43_573)&v_node_43_573!=null -->  H1(v_node_43_573)&true;
 H1a(y)&true -->  H1a(y)&true;
 x::node<val_43_558,v_node_43_573> * G2(v_node_43_573,y) * H1a(y)&
v_node_43_573!=null -->  G2(x,y) * H1a(y)&true;
 H1a(y)&true -->  H1a(y)&true
}
hpdefs [H1,H1a,G2][]: {
 HP_597(y_595_596,y_595)&true -->  
 emp&y_595_596=y_595
 or y_595_596::node<val_43_556,y_595_600> * HP_597(y_595_600,y_595)&true
 ;
 HP_603(next_43_532')&true -->  
 emp&next_43_532'=null
 or next_43_532'::node<val_43_531',next_43_606> * HP_603(next_43_606)&true
 ;
 HP_550(v_node_43_593)&true -->  
 v_node_43_593::node<val_43_531',next_43_532'> * 
 next_43_532'::node<val_43_531',next_43_583>&next_43_583=null
 or v_node_43_593::node<val_43_531',next_43_532'> * 
    next_43_532'::node<val_43_531',next_43_584> * 
    next_43_584::node<val_43_531',next_43_585>&next_43_585=null
 or v_node_43_593::node<val_43_531',next_43_532'> * 
    next_43_532'::node<val_43_531',next_43_586> * 
    next_43_586::node<val_43_531',next_43_587>&next_43_587=null
 or v_node_43_593::node<val_43_531',next_43_588>&next_43_588=null
 or v_node_43_593::node<val_43_531',next_43_589> * 
    next_43_589::node<val_43_531',next_43_590>&next_43_590=null
 or v_node_43_593::node<val_43_531',next_43_591> * 
    next_43_591::node<val_43_531',next_43_592>&next_43_592=null
 or emp&v_node_43_593=null
 ;
 G2(x_594,y_595)&true -->  x_594::node<val_43_556,y_595_596> * HP_597(y_595_596,y_595)&true;
 H1(x_602)&true -->  x_602::node<val_43_531',next_43_532'> * HP_603(next_43_532')&true;
 H1a(y)&true -->  htrue&true
}
]


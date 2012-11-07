HeapPred HP_604(node next_51_533').
HeapPred HP_598(node y_596_597, node y_596).
HeapPred HP_551(node next_51_533').
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
 H1a(y) * HP_551(v_node_51_568) * x::node<val_51_557,y>&v_node_51_568=null -->  G2(x,y)&true;
 H1(x)&true -->  x::node<val_51_532',next_51_533'> * HP_551(next_51_533')&true;
 HP_551(v_node_51_574)&v_node_51_574!=null -->  H1(v_node_51_574)&true;
 H1a(y)&true -->  H1a(y)&true;
 x::node<val_51_559,v_node_51_574> * G2(v_node_51_574,y)&v_node_51_574!=null -->  G2(x,y)&true
}
hpdefs [H1,H1a,G2]: {
 HP_598(y_596_597,y_596)&true -->  
 emp&y_596_597=y_596
 or y_596_597::node<val_51_557,y_596_601> * HP_598(y_596_601,y_596)&true
 ;
 HP_604(next_51_533')&true -->  
 emp&next_51_533'=null
 or next_51_533'::node<val_51_532',next_51_607> * HP_604(next_51_607)&true
 ;
 HP_551(v_node_51_594)&true -->  
 v_node_51_594::node<val_51_532',next_51_584>&next_51_584=null
 or v_node_51_594::node<val_51_532',next_51_585> * 
    next_51_585::node<val_51_532',next_51_586>&next_51_586=null
 or v_node_51_594::node<val_51_532',next_51_587> * 
    next_51_587::node<val_51_532',next_51_588>&next_51_588=null
 or v_node_51_594::node<val_51_532',next_51_533'> * 
    next_51_533'::node<val_51_532',next_51_589>&next_51_589=null
 or v_node_51_594::node<val_51_532',next_51_533'> * 
    next_51_533'::node<val_51_532',next_51_590> * 
    next_51_590::node<val_51_532',next_51_591>&next_51_591=null
 or v_node_51_594::node<val_51_532',next_51_533'> * 
    next_51_533'::node<val_51_532',next_51_592> * 
    next_51_592::node<val_51_532',next_51_593>&next_51_593=null
 or emp&v_node_51_594=null
 ;
 G2(x_595,y_596)&true -->  x_595::node<val_51_557,y_596_597> * HP_598(y_596_597,y_596)&y_596=H1a_y_609;
 H1(x_603)&true -->  x_603::node<val_51_532',next_51_533'> * HP_604(next_51_533')&true;
 H1a(y)&true -->  htrue&true
}
]


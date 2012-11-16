HeapPred HP_604(node next_54_533').
HeapPred HP_598(node y_596_597, node y_596).
HeapPred HP_551(node next_54_533').
HeapPred HP1(node a, node b).
HeapPred H2(node a, node b).
HeapPred H1b(node a).
HeapPred H1a(node a).
HeapPred H1(node a).
HeapPred G3(node b, node c, node d).
HeapPred G1(node a).
HeapPred G2(node a, node b).

append:SUCCESS[
ass [H1,H1a,H1b,G2][]: {
 H1a(y) * HP_551(v_node_54_568) * x::node<val_54_557,y>&v_node_54_568=null -->  G2(x,y) * H1b(y)&true;
 emp&v_node_54_568=null -->  H1b(y)&true;
 H1(x)&true -->  x::node<val_54_532',next_54_533'> * HP_551(next_54_533')&true;
 HP_551(v_node_54_574)&v_node_54_574!=null -->  H1(v_node_54_574)&true;
 H1a(y)&true -->  H1a(y)&true;
 x::node<val_54_559,v_node_54_574> * G2(v_node_54_574,y) * H1b(y)&
v_node_54_574!=null -->  G2(x,y) * H1b(y)&true;
 H1a(y)&true -->  H1b(y)&true
}
hpdefs [H1,H1a,H1b,G2][]: {
 HP_598(y_596_597,y_596)&true -->  
 emp&y_596_597=y_596
 or y_596_597::node<val_54_557,y_596_601> * HP_598(y_596_601,y_596)&true
 ;
 HP_604(next_54_533')&true -->  
 emp&next_54_533'=null
 or next_54_533'::node<val_54_532',next_54_607> * HP_604(next_54_607)&true
 ;
 HP_551(v_node_54_594)&true -->  
 v_node_54_594::node<val_54_532',next_54_533'> * 
 next_54_533'::node<val_54_532',next_54_584>&next_54_584=null
 or v_node_54_594::node<val_54_532',next_54_533'> * 
    next_54_533'::node<val_54_532',next_54_585> * 
    next_54_585::node<val_54_532',next_54_586>&next_54_586=null
 or v_node_54_594::node<val_54_532',next_54_533'> * 
    next_54_533'::node<val_54_532',next_54_587> * 
    next_54_587::node<val_54_532',next_54_588>&next_54_588=null
 or v_node_54_594::node<val_54_532',next_54_589>&next_54_589=null
 or v_node_54_594::node<val_54_532',next_54_590> * 
    next_54_590::node<val_54_532',next_54_591>&next_54_591=null
 or v_node_54_594::node<val_54_532',next_54_592> * 
    next_54_592::node<val_54_532',next_54_593>&next_54_593=null
 or emp&v_node_54_594=null
 ;
 G2(x_595,y_596)&true -->  x_595::node<val_54_557,y_596_597> * HP_598(y_596_597,y_596)&true;
 H1(x_603)&true -->  x_603::node<val_54_532',next_54_533'> * HP_604(next_54_533')&true;
 H1a(y)&true -->  emp&y=H1b_y_609;
 H1b(y)&true -->  htrue&true
}
]


HeapPred HP_616(node next_42_562').
HeapPred HP_611(node y_610, node y).
HeapPred HP_580(node next_42_562', node x').
HeapPred HP1(node a, node b).
HeapPred H2(node a, node b).
HeapPred H1a(node a).
HeapPred H1(node a).
HeapPred G3(node b, node c, node d).
HeapPred G1(node a).
HeapPred G2(node a, node b).

append[
ass [H1,H1a,G2]: {
 H1a(y) * HP_580(v_node_42_597,x) * x::node<val_42_586,y>&v_node_42_597=null -->  G2(x,y) * H1a(y)&true;
 emp&true -->  H1a(y)&true;
 H1(x)&true -->  x::node<val_42_561',next_42_562'> * HP_580(next_42_562',x)&true;
 HP_580(v_node_42_603,x)&v_node_42_603!=null -->  H1(v_node_42_603)&true;
 H1a(y)&true -->  H1a(y)&true;
 x::node<val_42_588,v_node_42_603> * G2(v_node_42_603,y) * H1a(y)&
v_node_42_603!=null -->  G2(x,y) * H1a(y)&true;
 emp&true -->  H1a(y)&true
}
hpdefs [H1,H1a,G2]: {
 HP_580(v_node_42_597)&true -->  
 v_node_42_597::node<val_42_561',next_42_562'> * HP_616(next_42_562')&true
 or emp&v_node_42_597=null
 ;
 G2(x,y)&true -->  x::node<val_42_586,y_610> * HP_611(y_610,y)&true;
 H1(x)&true -->  x::node<val_42_561',next_42_562'> * HP_616(next_42_562')&true;
 HP_611(y_610,y)&true -->  
 emp&y_610=y
 or y_610::node<val_42_586,y_614> * HP_611(y_614,y)&true
 ;
 HP_616(next_42_562')&true -->  
 emp&next_42_562'=null
 or next_42_562'::node<val_42_561',next_42_619> * HP_616(next_42_619)&true
 ;
 H1a(y)&true -->  htrue&true
}
]


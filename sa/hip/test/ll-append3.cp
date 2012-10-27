HeapPred HP_648(node next_80_580').
HeapPred HP_643(node y_642, node y).
HeapPred HP_603(node next_80_580', node x').
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
 HP_603(v_node_80_620,x) * x::node<val_80_609,y>&v_node_80_620=null -->  G1(x,y)&true;
 H1(x)&true -->  x::node<val_80_579',next_80_580'> * HP_603(next_80_580',x)&true;
 HP_603(v_node_80_626,x)&v_node_80_626!=null -->  H1(v_node_80_626)&true;
 x::node<val_80_611,v_node_80_626> * G1(v_node_80_626,y)&
v_node_80_626!=null & y!=null -->  G1(x,y)&true
}
hpdefs [H1,G1]: {
 HP_603(v_node_80_620)&true -->  
 HP_648(next_80_580')&true
 or emp&v_node_80_620=null
 ;
 HP_643(y_642,y)&true -->  
 emp&y_642=y
 or y_642::node<val_80_609,y_646> * HP_643(y_646,y)&y!=null
 ;
 HP_648(next_80_580')&true -->  
 emp&next_80_580'=null
 or next_80_580'::node<val_80_579',next_80_651> * HP_648(next_80_651)&true
 ;
 G1(x,y)&true -->  x::node<val_80_609,y_642> * HP_643(y_642,y)&true;
 H1(x)&true -->  x::node<val_80_579',next_80_580'> * HP_648(next_80_580')&true
}
]


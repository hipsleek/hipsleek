HeapPred HP_651(node next_80_650).
HeapPred HP_644(node y_643, node y).
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
 x::node<val_80_611,v_node_80_626> * G1(v_node_80_626,y) * 
y::node<a,flted_75_602>&flted_75_602=null & v_node_80_626!=null -->  G1(x,y)&true
}
hpdefs [H1,G1]: {
 HP_603(v_node_80_620)&true -->  
 v_node_80_620::node<val_80_649,next_80_650> * HP_651(next_80_650)&true
 or v_node_80_620::node<val_80_579',next_80_580'> * 
    next_80_580'::node<val_80_649,next_80_650> * HP_651(next_80_650)&true
 or emp&v_node_80_620=null
 ;
 G1(x,y)&true -->  x::node<val_80_642,y_643> * HP_644(y_643,y)&true;
 H1(x)&true -->  x::node<val_80_649,next_80_650> * HP_651(next_80_650)&true;
 HP_644(y_643,y)&true -->  
 emp&y_643=y
 or y_643::node<val_80_642,y_647> * HP_644(y_647,y) * 
    y::node<a,flted_75_602>&flted_75_602=null
 ;
 HP_651(next_80_650)&true -->  
 emp&next_80_650=null
 or next_80_650::node<val_80_649,next_80_654> * HP_651(next_80_654)&true
 
}
]


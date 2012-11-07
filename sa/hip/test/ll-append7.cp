HeapPred HP_633(node next_32_562').
HeapPred HP_627(node y_625_626, node y_625).
HeapPred HP_580(node next_32_562').
HeapPred HP1(node a, node b).
HeapPred H2(node a, node b).
HeapPred H1(node a).
HeapPred G3(node b, node c, node d).
HeapPred G1(node a).
HeapPred G2(node a, node b).

append[
ass [H1,G2]: {
 HP_580(v_node_32_597) * x::node<val_32_586,y>&v_node_32_597=null & y=null -->  G2(x,y)&true;
 H1(x)&true -->  x::node<val_32_561',next_32_562'> * HP_580(next_32_562')&true;
 HP_580(v_node_32_603)&v_node_32_603!=null -->  H1(v_node_32_603)&true;
 x::node<val_32_588,v_node_32_603> * G2(v_node_32_603,y)&
v_node_32_603!=null & y=null -->  G2(x,y)&true
}
hpdefs [H1,G2]: {
 HP_627(y_625_626,y_625)&true -->  
 emp&y_625_626=y_625
 or y_625_626::node<val_32_586,y_625_630> * HP_627(y_625_630,y_625)&true
 ;
 HP_633(next_32_562')&true -->  
 emp&next_32_562'=null
 or next_32_562'::node<val_32_561',next_32_636> * HP_633(next_32_636)&true
 ;
 HP_580(v_node_32_623)&true -->  
 v_node_32_623::node<val_32_561',next_32_613>&next_32_613=null
 or v_node_32_623::node<val_32_561',next_32_614> * 
    next_32_614::node<val_32_561',next_32_615>&next_32_615=null
 or v_node_32_623::node<val_32_561',next_32_616> * 
    next_32_616::node<val_32_561',next_32_617>&next_32_617=null
 or v_node_32_623::node<val_32_561',next_32_562'> * 
    next_32_562'::node<val_32_561',next_32_618>&next_32_618=null
 or v_node_32_623::node<val_32_561',next_32_562'> * 
    next_32_562'::node<val_32_561',next_32_619> * 
    next_32_619::node<val_32_561',next_32_620>&next_32_620=null
 or v_node_32_623::node<val_32_561',next_32_562'> * 
    next_32_562'::node<val_32_561',next_32_621> * 
    next_32_621::node<val_32_561',next_32_622>&next_32_622=null
 or emp&v_node_32_623=null
 ;
 G2(x_624,y_625)&true -->  x_624::node<val_32_586,y_625_626> * HP_627(y_625_626,y_625)&y_625=null;
 H1(x_632)&true -->  x_632::node<val_32_561',next_32_562'> * HP_633(next_32_562')&true
}
]


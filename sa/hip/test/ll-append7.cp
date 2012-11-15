HeapPred HP_634(node next_32_562').
HeapPred HP_628(node y', node y_626).
HeapPred HP_580(node next_32_562').
HeapPred HP1(node a, node b).
HeapPred H2(node a, node b).
HeapPred H1(node a).
HeapPred G3(node b, node c, node d).
HeapPred G1(node a).
HeapPred G2(node a, node b).

#append:SUCCESS[
ass [H1,G2]: {
 HP_580(v_node_32_597) * x::node<val_32_586,y'>&v_node_32_597=null & 
y=null & y'=null -->  G2(x,y)&true;
 H1(x)&true -->  x::node<val_32_561',next_32_562'> * HP_580(next_32_562')&true;
 HP_580(v_node_32_603)&v_node_32_603!=null -->  H1(v_node_32_603)&true;
 x::node<val_32_588,v_node_32_603> * G2(v_node_32_603,y')&
v_node_32_603!=null & y=null & y'=null -->  G2(x,y)&true
}
hpdefs [H1,G2]: {
 HP_628(y',y_626)&true -->  
 emp&y'=null
 or y'::node<val_32_586,y_631> * HP_628(y_631,y_627)&true
 ;
 HP_634(next_32_562')&true -->  
 emp&next_32_562'=null
 or next_32_562'::node<val_32_561',next_32_637> * HP_634(next_32_637)&true
 ;
 HP_580(v_node_32_624)&true -->  
 v_node_32_624::node<val_32_561',next_32_562'> * 
 next_32_562'::node<val_32_561',next_32_614>&next_32_614=null
 or v_node_32_624::node<val_32_561',next_32_562'> * 
    next_32_562'::node<val_32_561',next_32_615> * 
    next_32_615::node<val_32_561',next_32_616>&next_32_616=null
 or v_node_32_624::node<val_32_561',next_32_562'> * 
    next_32_562'::node<val_32_561',next_32_617> * 
    next_32_617::node<val_32_561',next_32_618>&next_32_618=null
 or v_node_32_624::node<val_32_561',next_32_619>&next_32_619=null
 or v_node_32_624::node<val_32_561',next_32_620> * 
    next_32_620::node<val_32_561',next_32_621>&next_32_621=null
 or v_node_32_624::node<val_32_561',next_32_622> * 
    next_32_622::node<val_32_561',next_32_623>&next_32_623=null
 or emp&v_node_32_624=null
 ;
 G2(x_625,y_626)&true -->  x_625::node<val_32_586,y'> * HP_628(y',y_626)&y_626=null;
 H1(x_633)&true -->  x_633::node<val_32_561',next_32_562'> * HP_634(next_32_562')&true
}
]


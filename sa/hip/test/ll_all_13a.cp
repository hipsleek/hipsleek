HeapPred HP_602(node next_86_572').
HeapPred HP_597(node next_85_569').
HeapPred G3(node a, node b, node c).
HeapPred G2(node a, node b).
HeapPred G1(node a).
HeapPred G(node a, node b).
HeapPred H3(node a, node b, node c).
HeapPred H2(node a, node b).
HeapPred H1(node a).
HeapPred H(node a).

delete_mid[
ass [H1,G2]: {
 H1(x)&x=null & v_node_82_567'=null -->  G2(x,v_node_82_567')&true;
 H1(x)&x!=null -->  x::node<val_85_568',next_85_569'> * HP_597(next_85_569')&true;
 HP_597(v_node_85_570') * x::node<val_85_620,v_node_85_570'>&true -->  G2(x,v_node_85_570')&true;
 H1(x)&x!=null -->  x::node<val_86_571',next_86_572'> * HP_602(next_86_572')&true;
 HP_602(next_86_609)&true -->  H1(next_86_609)&true;
 x::node<v_int_86_625,next_86_609> * G2(next_86_609,v_node_86_626) * 
v_node_86_578'::node<v_int_86_625,v_node_86_626>&true -->  G2(x,v_node_86_578')&true
}
hpdefs [H1,G2]: {
 HP_597(v_node_85_651)&true -->  G2(x,v_node_85_651)&true;
 HP_602(next_86_652)&true -->  
 next_86_652::node<val_85_568',next_85_569'>&next_85_569'=null
 or next_86_652::node<val_85_568',next_85_569'>&true
 or next_86_652::node<val_85_568',next_85_569'> * 
    next_85_569'::node<v_int_86_625,v_node_86_647>&v_node_86_647=null
 or H1(next_86_652)&true
 ;
 H1(x_650)&true -->  
 emp&x_650=null
 or x_650::node<val_86_571',next_86_572'> * H1(next_86_572')&true
 ;
 G2(x_653,v_node_82_654)&true -->  
 emp&v_node_82_654=null & x_653=null
 or x_653::node<val_85_620,v_node_82_654>
 or x_653::node<v_int_86_625,next_86_609> * G2(next_86_609,v_node_86_626) * 
    v_node_82_654::node<v_int_86_625,v_node_86_626>&true
 
}
]


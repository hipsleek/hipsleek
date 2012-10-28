HeapPred HP_629(node next_37_567').
HeapPred HP_624(node y_623, node y).
HeapPred HP_634(node v_node_37_611).
HeapPred HP_588(node next_37_567', node x').
HeapPred HP1(node a, node b).
HeapPred H2(node a, node b).
HeapPred H1(node a).
HeapPred G3(node b, node c, node d).
HeapPred G1(node a).
HeapPred G2(node a, node b).
HeapPred H(node a).

append[
ass [H1,G2]: {
 y::node<a,flted_34_587> * HP_588(v_node_37_605,x) * x::node<val_37_594,y>&
flted_34_587=null & v_node_37_605=null -->  G2(x,y)&true;
 H1(x)&true -->  x::node<val_37_566',next_37_567'> * HP_588(next_37_567',x)&true;
 HP_588(v_node_37_611,x)&v_node_37_611!=null -->  H1(v_node_37_611)&true;
 x::node<val_37_596,v_node_37_611> * G2(v_node_37_611,y) * 
y::node<a,flted_34_587>&flted_34_587=null & v_node_37_611!=null -->  G2(x,y)&true
}
hpdefs [H1,G2]: {
 HP_634(v_node_37_605)&true -->  
 HP_629(next_37_567')&true
 or emp&v_node_37_605=null
 ;
 HP_624(y_623,y)&true -->  
 emp&y_623=y
 or y_623::node<val_37_594,y_627> * HP_624(y_627,y)&true
 ;
 HP_629(next_37_567')&true -->  
 emp&next_37_567'=null
 or next_37_567'::node<val_37_566',next_37_632> * HP_629(next_37_632)&true
 ;
 G2(x,y)&true -->  x::node<val_37_594,y_623> * y::node<a,flted_34_587> * HP_624(y_623,y)&
flted_34_587=null;
 H1(x)&true -->  x::node<val_37_566',next_37_567'> * HP_629(next_37_567')&true
}
]


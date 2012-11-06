HeapPred HP_634(node next_37_567').
HeapPred HP_628(node y_626_627, node y_626).
HeapPred HP_639(node v_node_37_611).
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
 HP_639(v_node_37_624)&true -->  
 emp&v_node_37_624=null
 or HP_634(next_37_567')&true
 ;
 HP_628(y_626_627,y_626)&true -->  
 y_626_627::node<val_37_594,y_626_631> * HP_628(y_626_631,y_626)&true
 or emp&y_626_627=y_626
 ;
 HP_634(next_37_567')&true -->  
 next_37_567'::node<val_37_566',next_37_637> * HP_634(next_37_637)&true
 or emp&next_37_567'=null
 ;
 G2(x_625,y_626)&true -->  x_625::node<val_37_594,y_626_627> * y_626::node<a,flted_34_587> * 
HP_628(y_626_627,y_626)&flted_34_587=null;
 H1(x_633)&true -->  x_633::node<val_37_566',next_37_567'> * HP_634(next_37_567')&true
}
]


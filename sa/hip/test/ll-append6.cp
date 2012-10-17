HeapPred HP_632(node next_37_631).
HeapPred HP_625(node flted_34_624, node y).
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
flted_34_587=null & v_node_37_605=null ->  G2(x,y)&true,
 H1(x)&true ->  x::node<val_37_566',next_37_567'> * HP_588(next_37_567',x)&true,
 HP_588(v_node_37_611,x)&v_node_37_611!=null ->  H1(v_node_37_611)&true,
 x::node<val_37_596,v_node_37_611> * G2(v_node_37_611,y) * 
y::node<a,flted_34_587>&flted_34_587=null & v_node_37_611!=null ->  G2(x,y)&true
}
hpdefs [H1,G2]: {
 HP_588(v_node_37_605)&true ->  
 v_node_37_605::node<val_37_630,next_37_631> * HP_632(next_37_631)&true
 or v_node_37_605::node<val_37_566',next_37_567'> * 
    next_37_567'::node<val_37_630,next_37_631> * HP_632(next_37_631)&true
 or emp&v_node_37_605=null
 ,
 G2(x,y)&true ->  x::node<val_37_594,y> * y::node<a_623,flted_34_624> * 
HP_625(flted_34_624,y)&true,
 H1(x)&true ->  x::node<val_37_630,next_37_631> * HP_632(next_37_631)&true,
 HP_625(flted_34_624,y)&true ->  
 emp&flted_34_624=null
 or y::node<val_37_594,y> * y::node<a_623,flted_34_628> * 
    HP_625(flted_34_628,y)&flted_34_624=null
 ,
 HP_632(next_37_631)&true ->  
 emp&next_37_631=null
 or next_37_631::node<val_37_630,next_37_635> * HP_632(next_37_635)&true
 
}
]


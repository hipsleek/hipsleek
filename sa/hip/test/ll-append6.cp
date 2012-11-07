HeapPred HP_647(node next_37_567').
HeapPred HP_641(node y_639_640, node y_639).
HeapPred HP_588(node next_37_567').
HeapPred HP1(node a, node b).
HeapPred H2(node a, node b).
HeapPred H1(node a).
HeapPred G3(node b, node c, node d).
HeapPred G1(node a).
HeapPred G2(node a, node b).
HeapPred H(node a).

append[
ass [H1,G2]: {
 y::node<a,flted_34_587> * HP_588(v_node_37_605) * x::node<val_37_594,y>&
v_node_37_605=null & flted_34_587=null -->  G2(x,y)&true;
 H1(x)&true -->  x::node<val_37_566',next_37_567'> * HP_588(next_37_567')&true;
 HP_588(v_node_37_611)&v_node_37_611!=null -->  H1(v_node_37_611)&true;
 x::node<val_37_596,v_node_37_611> * G2(v_node_37_611,y) * 
y::node<a,flted_34_587>&v_node_37_611!=null & flted_34_587=null -->  G2(x,y)&true
}
hpdefs [H1,G2]: {
 HP_641(y_639_640,y_639)&true -->  
 emp&y_639_640=y_639
 or y_639_640::node<val_37_594,y_639_644> * HP_641(y_639_644,y_639)&true
 ;
 HP_647(next_37_567')&true -->  
 emp&next_37_567'=null
 or next_37_567'::node<val_37_566',next_37_650> * HP_647(next_37_650)&true
 ;
 HP_588(v_node_37_637)&true -->  
 v_node_37_637::node<val_37_566',next_37_627>&next_37_627=null
 or v_node_37_637::node<val_37_566',next_37_628> * 
    next_37_628::node<val_37_566',next_37_629>&next_37_629=null
 or v_node_37_637::node<val_37_566',next_37_630> * 
    next_37_630::node<val_37_566',next_37_631>&next_37_631=null
 or v_node_37_637::node<val_37_566',next_37_567'> * 
    next_37_567'::node<val_37_566',next_37_632>&next_37_632=null
 or v_node_37_637::node<val_37_566',next_37_567'> * 
    next_37_567'::node<val_37_566',next_37_633> * 
    next_37_633::node<val_37_566',next_37_634>&next_37_634=null
 or v_node_37_637::node<val_37_566',next_37_567'> * 
    next_37_567'::node<val_37_566',next_37_635> * 
    next_37_635::node<val_37_566',next_37_636>&next_37_636=null
 or emp&v_node_37_637=null
 ;
 G2(x_638,y_639)&true -->  x_638::node<val_37_594,y_639_640> * y_639::node<a,flted_34_587> * 
HP_641(y_639_640,y_639)&flted_34_587=null;
 H1(x_646)&true -->  x_646::node<val_37_566',next_37_567'> * HP_647(next_37_567')&true
}
]


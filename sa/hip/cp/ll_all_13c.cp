HeapPred HP_607(node a,node b).
HeapPred HP_700(node a,node b).
HeapPred HP_577(node a).
HeapPred HP_582(node a).
HeapPred HP_643(node a).

trav[
ass [H1,G1]:{
 G1(v_node_95_605) * x'::node<val_95_588,v_node_95_605>& true --> G1(x');
 HP_577(v_node_93_557') --> G1(v_node_93_557');
 HP_582(v_node_95_560')&true --> H1(v_node_95_560');
 H1(x) --> x::node<val_95_558',next_95_559'> * HP_582(next_95_559');
 H1(x)&true --> x::node<val_93_555',next_93_556'> * HP_577(next_93_556')
 }

hpdefs [H1,G1]:{
    HP_643(p) --> p::node<_,next_129_652> * HP_643(next_129_652)
     or p::node<_,p1> * G1(p1);
    G1(res) --> G1(p) * res::node<_,p>;
    H1(x) --> x::node<_,next_129_556'> * HP_643(next_129_556')
 }
]

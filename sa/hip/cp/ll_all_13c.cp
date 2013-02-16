HeapPred HP_607(node a,node b).
HeapPred HP_700(node a,node b).
HeapPred HP_577(node a).
HeapPred HP_582(node a).
HeapPred HP_643(node a).
HeapPred HP_603(node a).

trav:SUCCESS[
ass [H1,G1][]:{
 G1(v_node_95_605) * x'::node<val_95_588,v_node_95_605>& true --> G1(x');
 HP_582(v_node_93_557') --> G1(v_node_93_557');
 HP_582(v_node_95_560')&true --> H1(v_node_95_560');
 //H1(x) --> x::node<val_95_558',next_95_559'> * HP_582(next_95_559');
 H1(x)&true --> x::node<val_93_555',next_93_556'> * HP_582(next_93_556')
 }

hpdefs [H1,G1][]:{
    HP_643(next_90_565') --> HP_603(next_90_565')
       or next_90_565'::node<val_90_564',next_90_648>@M * HP_643(next_90_648);
    HP_603(res_650) --> HP_643(next_90_565')&true
     or res_650::node<val_92_612,v_node_92_642>@M * HP_603(v_node_92_642);
    HP_643(p) --> p::node<_,next_129_652> * HP_643(next_129_652);
     //or p::node<_,p1> * G1(p1);
    G1(res) --> //HP_643(res);
      G1(p) * res::node<_,p>;
    H1(x) --> x::node<_,next_129_556'> * HP_643(next_129_556')
 }
]

HeapPred HP_607(node a,node b).
HeapPred HP_700(node a,node b).
HeapPred HP_577(node a).
HeapPred HP_582(node a).
HeapPred HP_643(node a).

trav:SUCCESS[
ass [H1,G2][]:{
 G2(v_node_131_605,v_node_131_595) * x::node<val_131_588,v_node_131_605>&
  v_node_132_564'=x --> G2(v_node_132_564',x);
 HP_577(v_node_129_557') * x::node<_,v_node_129_557'> --> G2(v_node_129_557',x);
 HP_577(v_node_131_560')&true --> H1(v_node_131_560');
 H1(x) --> x::node<_,next_129_556'> * HP_577(next_129_556')
 }

hpdefs [H1,G2][]:{
    HP_700(p,_) --> p::node<_,next_129_652> * HP_700(next_129_652,_);
    HP_643(p) --> p::node<_,next_129_652> * HP_643(next_129_652);
    G2(res,x_663) --> HP_700(p,x_663) * res::node<_,p> & res=x_663;
    H1(x) --> x::node<_,next_129_556'> * HP_643(next_129_556')
 }
]

HeapPred HP_597(node a).
HeapPred HP_602(node a).

delete_mid[
ass [H1,G2]:{
  x::node<v_int_86_625,next_86_609> * G2(next_86_609,v_node_86_626) * 
  v_node_86_578'::node<v_int_86_625,v_node_86_626>&
  true --> G2(x,v_node_86_578');
 HP_597(v_node_85_570') * x::node<val_85_620,v_node_85_570'> --> G2(x,v_node_85_570');
 H1(x)&x=null & v_node_82_567'=null --> G2(x,v_node_82_567');
 HP_602(next_86_609)&true --> H1(next_86_609);
 H1(x)&x!=null --> x::node<val_86_571',next_86_572'> * HP_602(next_86_572');
 H1(x)&x!=null --> x::node<val_85_568',next_85_569'> * HP_597(next_85_569')
 }

hpdefs [H1,G2]:{
  H1(x) --> x=null or x::node<_,p> * H1(p);
  G2(x_653,res_654) --> res_654=null & x_653=null
    or x_653::node<_,res_654>
    or x_653::node<_,next_86_609> * G2(next_86_609,v_node_86_626) *
       res_654::node<_,v_node_86_626>
 }
]

/*
G2(x1,v) --> x1::node<_,next_81_597> * G2(next_81_597,v_node_81_614)* v::node<_,v_node_81_614>
        or emp&x1=null & v=null
*/

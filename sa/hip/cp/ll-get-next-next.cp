HeapPred HP_2(node a, node b).
HeapPred HP_2a(node a, node b).
HeapPred HP_1(node a).

get_next_next[
ass [H1,G1]:{
  HP_2(v_node_28_533',v_node_26_566) * x::node<val_26_551,v_node_26_566> *
  v_node_26_566::node<val_26_565,next_27_532'>& next_27_532'=null --> G1(x,v_node_28_533');
  HP_2a(v_node_26_524',x) --> v_node_26_524'::node<val_26_525',next_26_526'> *
  HP_2(next_26_526',v_node_26_524');
  H1(x) --> x::node<val_26_522',next_26_523'> * HP_2a(next_26_523',x)


 }

hpdefs [H1,G1]:{
 HP_1(v_node_28_533') --> htrue&true;
 G1(x,v_node_28_533') --> x::node<_,v_node_26_566> * v_node_26_566::node<_,next_27_532'> * HP_1(v_node_28_533')&
      next_27_532'=null;
 H1(x) --> x::node<val_26_522',next_26_523'> *next_26_523'::node<val_26_579,next_26_526'>

 }
]

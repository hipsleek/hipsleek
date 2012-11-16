HeapPred HP_588(node a).
HeapPred HP_580(node a).
HeapPred HP_1(node a).

get_next_next:SUCCESS[
ass [H1,G1][]:{
  HP_588(v_node_28_542') * x::node<_,v_node_26_602> * v_node_26_602::node<_,next_27_541'>& next_27_541'=null --> G1(x,v_node_28_542');
 HP_580(v_node_26_533') --> v_node_26_533'::node<val_26_534',next_26_535'> *  HP_588(next_26_535');
 H1(x) --> x::node<val_26_531',next_26_532'> * HP_580(next_26_532')


 }

hpdefs [H1,G1][]:{
 G1(x,res) --> x::node<_,p1> * p1::node<_,p2> & res=unk_HP_1 & p2=null;
 H1(x) --> x::node<_,p3> *p3::node<_,unk_HP_1>

 }
]

/*
hpdefs [H1,G1]:{
 HP_1(v_node_28_533') --> htrue&true;
 G1(x,v_node_28_533') --> x::node<_,v_node_26_566> * v_node_26_566::node<_,next_27_532'> * HP_1(v_node_28_533')&
      next_27_532'=null;
 H1(x) --> x::node<val_26_522',p1> *p1::node<val_26_579,p2>*HP_1(p2)

 }
*/

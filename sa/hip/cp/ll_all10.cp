HeapPred HP_2(node a, node b).
HeapPred HP_2a(node a, node b).
HeapPred HP_1(node a).

get_next_next[
ass [H1,G2]:{
  x::node<_,p> *  HP_2a(y,p) * p::node<_,y> --> G2(x,y);
 HP_2(p1,x) --> p1::node<_,p2> * HP_2a(p2,p1);
 H1(x) --> x::node<_,p> * HP_2(p,x)
 }

hpdefs [H1,G2]:{
  G2(x,v_node_35_638) --> x::node<_,v_node_35_615> * v_node_35_615::node<_,v_node_35_638> & v_node_35_638=HP_608_v_node_35_639;
  H1(x) --> x::node<_,p1> * p1::node<_,HP_608_v_node_35_639>
 }
]

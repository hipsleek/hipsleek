HeapPred HP_1a( node b).
HeapPred HP_1b( node b).
HeapPred HP_1(node a).

get_next_next:SUCCESS[
ass [H1,G2][]:{
  x::node<_,p> *  HP_1b(y) * p::node<_,y> --> G2(x,y);
 HP_1a(p1) --> p1::node<_,p2> * HP_1b(p2);
 H1(x) --> x::node<_,p> * HP_1a(p)
 }

hpdefs [H1,G2][]:{
  G2(x,v_node_35_638) --> x::node<_,v_node_35_615> * v_node_35_615::node<_,v_node_35_638> & v_node_35_638=HP_608_v_node_35_639;
  H1(x) --> x::node<_,p1> * p1::node<_,HP_608_v_node_35_639>
 }
]

HeapPred HP_2(node a, node b).
HeapPred HP_1(node a).

get_next[
ass [H,G]:{
  HP_2(v_node_46_548',x) * x::node<val_44_568,next_45_547'>&next_45_547'=null --> G(x,v_node_46_548');
  H(x) --> x::node<val_44_543',next_44_544'> * HP_2(next_44_544',x)

 }

hpdefs [H,G]:{
  H(x) -->  x::node<val_44_543',next_44_544'> * HP_1(next_44_544');
  HP_1(x) --> htrue&true;
  G(x,v_node_46_548') --> HP_1(v_node_46_548') * x::node<val_44_568,next_45_547'>&next_45_547'=null
 }
]

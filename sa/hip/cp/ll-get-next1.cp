HeapPred HP_1a(node a).
HeapPred HP_1(node a).

get_next:SUCCESS[
ass [H,G][]:{
  HP_1a(p1) * x::node<_,p>&p=null --> G(x,p1);
  H(x) --> x::node<_,p> * HP_1a(p)

 }

hpdefs [H,G][]:{
  H(x) -->  x::node<_, HP_1> ;
  G(x,v_node_46_548') --> x::node<val_44_568,next_45_547'>&next_45_547'!=null & v_node_46_548'=HP_1
 }
]

/*
hpdefs [H,G]:{
  H(x) -->  x::node<val_44_543',next_44_544'> * HP_1(next_44_544');
  HP_1(x) --> htrue&true;
  G(x,v_node_46_548') --> HP_1(v_node_46_548') * x::node<val_44_568,next_45_547'>&next_45_547'=null
 }
*/

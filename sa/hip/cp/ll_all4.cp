HeapPred HP_1a(node a).
HeapPred HP_1(node a).

get_next:SUCCESS[
ass [H1,G2][]:{
   HP_1a(v_node_46_548') * x::node<val_44_568,next_45_547'>&next_45_547'=null --> G2(x,v_node_46_548');
  H1(x) --> x::node<val_44_543',next_44_544'> * HP_1a(next_44_544')

 }

hpdefs [H1,G2][]:{
  H1(x) -->  x::node<_,p>;
  G2(x,y) --> x::node<_,p1> & p1=null & y=p
 }
]

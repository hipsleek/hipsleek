HeapPred HP_2(node a, node b).
HeapPred HP_1(node a).

get_next[
ass [H,G3]:{
  HP_2(v_node_55_548',x) * x::node<val_53_568,next_54_547'>& next_54_547'=null --> G3(x,v_571,v_node_55_548')&x=v_571;
  H(x) --> x::node<val_53_543',next_53_544'> * HP_2(next_53_544',x)

 }

hpdefs [H,G]:{
  HP_1(x) --> htrue&true;
  G3(x,v_571,v_node_55_548') --> HP_1(v_node_55_548') * x::node<val_53_568,next_54_547'>& next_54_547'=null & x=v_571;
  H(x) --> x::node<val_53_543',next_53_544'> * HP_1(next_53_544')
 }
]

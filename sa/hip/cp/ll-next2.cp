HeapPred HP_2(node a, node b).
HeapPred HP_1(node a).

get_next:SUCCESS[
ass [H,G3][]:{
  HP_1(v_node_55_548') * x::node<val_53_568,next_54_547'> & x'=x & next_54_547'=null --> G3(x,x',v_node_55_548');
  H(x) --> x::node<val_53_543',next_53_544'> * HP_1(next_53_544')

 }

hpdefs [H,G][]:{
  G3(x,v_571,v_node_55_548') --> x::node<val_53_568,next_54_547'> & next_54_547'=null & x=v_571 &
   v_node_55_548' = unk_HP_1;
  H(x) --> x::node<val_53_543',next_53_544'> & next_53_544' = unk_HP_1
 }
]

/*
hpdefs [H,G]:{
  HP_1(x) --> htrue&true;
  G3(x,v_571,v_node_55_548') --> HP_1(v_node_55_548') * x::node<val_53_568,next_54_547'>& next_54_547'=null & x=v_571;
  H(x) --> x::node<val_53_543',next_53_544'> * HP_1(next_53_544')
 }
*/

HeapPred HP_2(node a, node b).
HeapPred HP_1(node a).

get_next[
ass [H1,G4]:{
  HP_2(v_node_28_529',x) * x::node<val_26_549,next_27_528'>& next_27_528'=null --> G4(v_node_28_529',x,v_552)&x=v_552;
  H1(x) --> x::node<val_26_524',next_26_525'> * HP_2(next_26_525',x)
 }

hpdefs [H,G]:{
  HP_1(v_node_28_529') --> htrue&true;
  G4(v_node_28_529',x,v_552) --> HP_1(v_node_28_529') * x::node<val_26_549,next_27_528'>&next_27_528'=null & x=v_552;
  H1(x) --> x::node<val_26_524',next_26_525'> * HP_1(next_26_525')

 }
]

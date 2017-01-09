HeapPred HP_1a(node a).
HeapPred HP_1(node a).

get_next:SUCCESS[
ass [H1,G4][]:{
  HP_1a(v_node_28_529') * x::node<val_26_549,next_27_528'> &
    x=x'& next_27_528'=null --> G4(v_node_28_529',x,x');
  H1(x) --> x::node<val_26_524',next_26_525'> * HP_1a(next_26_525')
 }

hpdefs [H,G][]:{
  HP_1(v_node_28_529') --> htrue&true;
  G4(res,x,v_552) --> x::node<val_26_549,next_27_528'>&next_27_528'=null & x=v_552 & res=unk_HP_1;
  H1(x) --> x::node<val_26_524',unk_HP_1>

 }
]

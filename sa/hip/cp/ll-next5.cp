HeapPred HP_1a(node b).
HeapPred HP_1(node a).

get_next:SUCCESS[
ass [H1,G4][]:{
  HP_1a(v_node_29_526') * x::node<val_28_543,v_node_29_526'>&x=x' --> G4(v_node_29_526',x,x');
  H1(x) -->  HP_1a(next_28_525') * x::node<val_28_524',next_28_525'>


 }

hpdefs [H1,G4][unk_HP_1]:{
  G4(res,x,v_544) --> x::node<val_28_524',res> & res=unk_HP_1 & x=v_544;
  H1(x) --> x::node<val_28_524',unk_HP_1>
 }
]
/*
hpdefs [H1,G4]:{
  G4(next_28_525',x,v_544) --> x::node<val_28_524',next_28_525'>*HP_1(next_28_525')&x=v_544;
  H1(x) --> x::node<val_28_524',p> * HP_1(p);
  HP_1(x) --> htrue&true
 }
*/

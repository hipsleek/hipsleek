HeapPred HP_541(node a, node b).
HeapPred HP_1a(node a).
HeapPred HP_1b(node a).
HeapPred HP_1c(node a).

get_next:SUCCESS[
ass [H1,G4][]:{
    HP_541(res,q) *  x'::node<_,res>&x=x' --> G4(res,x',x,p);
    H1(x,q)&true --> x::node<val_30_527',next_30_528'> *  HP_541(next_30_528',q)
 }

hpdefs [H1,G4][unk_HP_1a]:{
  G4(res,x,v_548,p) --> x::node<val_30_547,res> &x=v_548 &res= unk_HP_1a & p= unk_HP_1c;
  H1(x,q) --> x::node<val_28_524',unk_HP_1a> & q = unk_HP_1b
 }
]

/*

HP_2(v_node_31_529',q) * x::node<val_30_547,v_node_31_529'>&true --> G4(v_node_31_529',x,v_548,p)& x=v_548;
    H1(x,q) --> x::node<val_30_527',next_30_528'> * HP_2(next_30_528',q)

hpdefs [H1,G4]:{
  G4(res,x,v_548,p) --> x::node<val_30_547,res> * HP_1a(res) * HP_1c(p) &x=v_548;
  H1(x,q) --> x::node<val_28_524',p>*HP_1a(p)*HP_1b(q);
  HP_1a(x) --> htrue&true;
  HP_1b(x) --> htrue&true;
  HP_1c(x) --> htrue&true
 }
*/

HeapPred HP_925(node a).
HeapPred HP_952(tree a, tree b).
HeapPred HP_953(node a, tree b).
HeapPred HP_954(tree a, tree b).
HeapPred HP_955(tree a, node b).

check_tree:SUCCESS[
ass [H1,G1][]:{
 // BIND (0)
   H1(t) --> t::tree<val_33_923,children_33_924>@M * HP_925(children_33_924);
 // PRE_REC (2;0)
   HP_925(children_33_924) * t::tree<val_33_923,children_33_924>@M& children_33_924!=null --> H2(children_33_924,t);
 // POST (1;0)
   HP_925(children_33_924) * t::tree<val_33_923,children_33_924>@M& children_33_924=null --> G1(t);
 // POST (2;0)
  G2(children_33_924,t)&children_33_924!=null & t!=null --> G1(t)
 }

]

check_child:SUCCESS[
ass [H2,G2][]:{
 // BIND (2;0)
  H2(l,par)& l!=null --> l::node<child_47_949,next_47_950,parent_47_951>@M *HP_952(child_47_949,par) *
    HP_953(next_47_950,par) *HP_954(parent_47_951,par) * HP_955(par,l);
 // PRE_REC (1;2;0)
  HP_953(next_47_950,parent_47_951) * HP_954(parent_47_951,par) * HP_955(parent_47_951,l)&
   par=parent_47_951 --> H2(next_47_950,parent_47_951);
 // PRE_REC (1;2;0)
  HP_952(child_47_949,par) --> H1(child_47_949);
 // POST (1;0)
  H2(l,par)& l=null --> G2(l,par);
 // POST (1;2;0)
  l::node<child_47_949,next_47_950,par>@M * G2(next_47_950,par) --> G2(l,par);
 // POST
   HP_954(parent_47_951,par)& par=parent_47_951 --> emp
 }
hpdefs [H1,G1,G2][]:{
 G1(t_1248) <-> G2(children_33_924,t_1248)&t_1248!=null
   or t_1248::tree<val_33_923,children_33_924>@M&children_33_924=null;
 G2(l_1249,par_1250) <-> emp&l_1249=null
 or l_1249::node<child_47_949,next_47_950,par_1250>@M * G2(next_47_950,par_1250);
 H1(t_1093) <-> t_1093::tree<val_33_923,children_33_924>@M & children_33_924 = null
 }
]
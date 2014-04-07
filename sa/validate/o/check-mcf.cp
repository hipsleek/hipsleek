HeapPred HP_1048(node next_43_1044, node prv, tree par).
HeapPred HP_1046(tree child_43_1042, node prv, tree par).
HeapPred HP_1047(node prev_43_1043, node prv, tree par).
HeapPred HP_1049(tree parent_43_1045, node prv, tree par).
HeapPred HP_1166(node children_42_1073).

check_child:SUCCESS[
ass [H2,G2][]:{
 // BIND (2;0)
  H2(l,prv,par)&l!=null --> l::node<child,prev,next,parent>@M * HP_1046(child,prv,par)
  * HP_1047(prev,prv,par) * HP_1048(next,prv,par) * HP_1049(parent,prv,par)&true;
 // PRE_REC (1;1;2;0)
 HP_1048(next,prev,par)&prev=prv & par=parent |#| l::node<child,prev,next,par>@M&true --> H2(next,l,par)&true;
 // PRE_REC (1;1;1;2;0)
  HP_1046(child,prev,par)&prev=prv & par=parent --> H1(child)&true;
 // POST (1;0)
  H2(l,prv,par)&l=null --> G2(l,prv,par)& true;
 // POST (1;1;1;1;2;0)
 G2(next,l,par) * l::node<child,prev,next,par>@M * HP_1047(prev,prv,par) *
   HP_1049(parent,prv,par) * G1(child)& prev=prv & par=parent --> G2(l,prev,par)&true
 }
hpdefs [H1,G1][]:{
   H1(t) <-> t::tree<val,children>@M * H2(children,v',t)&v'=null;
 H2(l,prv,par) <-> l::node<child,prev,next,parent>@M * child::tree<val,children>@M *
  H2(next,l,par) * H2(children,v',child)&par=parent & prev=prv & v'=null or emp&l=null;
 G1(t) <-> t::tree<val,children>@M * G2(children,v,t)&v=null;
 G2(l,prv,par) <-> l::node<child,prv,next,par>@M * child::tree<val,children>@M * 
   G2(next,l,par) * G2(children,v,child)&v=null or emp&l=null
}
]

check_tree:SUCCESS[
ass [H1,G1][]:{
 // BIND (0)
  H1(t)&true --> t::tree<val,children>@M * HP_1166(children)&true;
 // PRE_REC (2;0)
  HP_1166(children)&children!=null & v'=null |#| t::tree<val,children>@M& true --> H2(children,v',t)&true;
 // POST (1;0)
  t::tree<val,children>@M * HP_1166(children)&children=null --> G1(t)& true;
 // POST (2;0)
  t::tree<val,children>@M * G2(children,v,t)&children!=null & v=null --> G1(t)&true
 }
]

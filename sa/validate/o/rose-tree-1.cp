HeapPred HP_947(node a).
HeapPred HP_974(tree a, tree b).
HeapPred HP_975(node a, tree b).
HeapPred HP_976(tree a, tree b).
HeapPred HP_955(tree a, node b).

check_tree:SUCCESS[
ass [H1,G1][]:{
  // BIND (0)
   H1(t) --> t::tree<val_33_945,children_33_946>@M * HP_947(children_33_946);
 // PRE_REC (2;0)
  HP_947(children_33_946)& children_33_946!=null |#| t::tree<val_33_945,children_33_946>@M --> H2(children_33_946,t);
 // POST (1;0)
  HP_947(children_33_946) * t::tree<val_33_945,children_33_946>@M& children_33_946=null --> G1(t);
 // POST (2;0)
  t::tree<val_33_945,children_33_946>@M * G2(children_33_946,t)& children_33_946!=null --> G1(t)
 }
  hpdefs [H1,G1][]:{
  G1(t_1188) <-> t_1188::tree<val_33_945,children_33_946>@M&children_33_946=null
    or t_1188::tree<val_33_945,children_33_946>@M * G2(children_33_946,t_1188)&
       children_33_946!=null;
  G2(l_1189,par_1190) <-> emp&l_1189=null
    or l_1189::node<child_47_971,next_47_972,par_1190>@M * G2(next_47_972,par_1190);
  H1(t_1159) <->
     t_1159::tree<val_33_945,children_33_946>@M * H2(children_33_946,t_1159)& children_33_946!=null
    or t_1159::tree<val_33_945,children_33_946>@M&children_33_946=null;
  H2(l_1186,par_1187) <-> H2(next_47_1061,par_1187) *  child_47_1060::tree<val_33_1058,children_33_1059>@M * 
     l_1186::node<child_47_1060,next_47_1061,parent_47_1062>@M& par_1187=parent_47_1062 & children_33_1059=null
    or H2(next_47_1061,par_1187) * child_47_1060::tree<val_33_1058,children_33_1059>@M * 
     l_1186::node<child_47_1060,next_47_1061,parent_47_1062>@M& par_1187=parent_47_1062 & children_33_1059!=null
    or emp&l_1186=null
 }
]

check_child:SUCCESS[
ass [H2,G2][]:{
 // BIND (2;0)
  H2(l,par)& l!=null --> l::node<child_47_971,next_47_972,parent_47_973>@M * 
   HP_974(child_47_971,par) * HP_975(next_47_972,par) * HP_976(parent_47_973,par);
 // PRE_REC (1;2;0)
  HP_975(next_47_972,parent_47_973)& par=parent_47_973 --> H2(next_47_972,parent_47_973);
 // PRE_REC (1;2;0)
  HP_974(child_47_971,parent_47_973)& par=parent_47_973 --> H1(child_47_971);
 // POST (1;0)
  H2(l,par)& l=null --> G2(l,par);
 // POST (1;2;0)
  HP_976(parent_47_973,par) * l::node<child_47_971,next_47_972,par>@M * G2(next_47_972,par)&
   par=parent_47_973 --> G2(l,par);
  // POST
   HP_976(parent_47_973,par)& par=parent_47_973 --> emp
 }

]

/*
G1(t_1188) ::= 
 t_1188::tree<val_33_945,children_33_946>@M&children_33_946=null
 or t_1188::tree<val_33_945,children_33_946>@M * G2(children_33_946,t_1188)&
    children_33_946!=null
 ,
 G2(l_1189,par_1190) ::= 
 emp&l_1189=null
 or l_1189::node<child_47_971,next_47_972,par_1190>@M * 
    G2(next_47_972,par_1190)
 ,
 H1(t_1159) ::= 
 t_1159::tree<val_33_945,children_33_946>@M * H2(children_33_946,t_1159)&
 children_33_946!=null
 or t_1159::tree<val_33_945,children_33_946>@M&children_33_946=null
 ,
 H2(l_1186,par_1187) ::= 
 H2(next_47_1061,par_1187) * 
 child_47_1060::tree<val_33_1058,children_33_1059>@M * 
 l_1186::node<child_47_1060,next_47_1061,parent_47_1062>@M&
 par_1187=parent_47_1062 & children_33_1059=null
 or H2(next_47_1061,par_1187) * 
    child_47_1060::tree<val_33_1058,children_33_1059>@M * 
    l_1186::node<child_47_1060,next_47_1061,parent_47_1062>@M&
    par_1187=parent_47_1062 & children_33_1059!=null
 or emp&l_1186=null
*/
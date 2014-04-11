HeapPred HP_958(node2 a, node2 b).
HeapPred HP_959(node2 a, node2 b).
HeapPred HP_1056(node2 a).
HeapPred HP_1057(node2 a).
HeapPred HP_1075(node2 a).

skip0:SUCCESS[
ass [H2][]:{
 // BIND
  H2(l,e)& e=l --> emp;
 // BIND (2;0)
  H2(l,e)&e!=l &  l!=null --> l::node2<val_32_955,n_32_956,s_32_957>@M * 
   HP_958(n_32_956,e) * HP_959(s_32_957,e);
 // PRE_REC (2;0)
   HP_958(n_32_956,e) --> H2(n_32_956,e);
 // POST (2;0)
   HP_959(s_32_957,e)& s_32_957=null --> emp
 }

hpdefs [H2][]:{
  H2(l,e) <-> l::lseg<e>
 }
]

skip1:SUCCESS[
ass [H1][]:{
 // BIND (2;0)
   H1(l)&l!=null --> l::node2<val_22_1053,n_22_1054,s_22_1055>@M *
     HP_1056(n_22_1054) * HP_1057(s_22_1055);
 // PRE_REC (2;0)
   HP_1057(s_22_1055) --> H1(s_22_1055);
 // PRE (2;0)
   HP_1056(n_22_1054) --> n_22_1054::lseg<s_22_1055>@M * HP_1075(s_22_1055);
 // POST (1;0)
  H1(l)& l=null --> emp
 }

hpdefs [H1][]:{
  H1(l) <-> l::skipll<>

 }
]

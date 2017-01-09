HeapPred HP_907(node2 a, node2 b).
HeapPred HP_908(node2 a, node2 b).

skip0:SUCCESS[
ass [SLSEG,G][]:{
 // BIND (2;2;0)
  SLSEG(l,e)&e!=l & l!=null --> l::node2<n_24_905,s_24_906>@M *
  HP_907(n_24_905,e) * HP_908(s_24_906,e);
 // PRE_REC (1;2;2;0)
  HP_907(n_24_905,e) --> SLSEG(n_24_905,e);
 // POST (1;0)
  SLSEG(l,e)& e=l --> G(l,e);
 // POST (1;2;2;0)
  HP_908(s_24_906,e) * l::node2<n_24_905,s_24_906>@M *G(n_24_905,e)&e!=l &
    s_24_906=null --> G(l,e)
 // POST
 // HP_908(s_24_906,e) & s_24_906=null --> emp
 // POST
 // SLSEG(l,e) & e=l --> emp;
 }

hpdefs [SLSEG,G][]:{
 G(l_961,e_962) <-> emp&e_962=l_961
   or l_961::node2<n_24_905,s_24_906>@M * G(n_24_905,e_962)&e_962!=l_961 &
    s_24_906=null;
 SLSEG(l_959,e_960) <-> emp&e_960=l_959
   or SLSEG(n_24_945,e_960) * l_959::node2<n_24_945,s_24_946>@M&
     s_24_946=null & e_960!=l_959

 }
]
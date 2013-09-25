HeapPred HP_891(node a, node b).
HeapPred HP_892(node a, node b).

check_csll:SUCCESS[
ass [H1,G1][]:{
 // BIND (2;0)
  H1(l,p)&l!=p --> l::node<val_20_889,next_20_890>@M * HP_891(next_20_890,p) *
    HP_892(p,l);
 // PRE_REC (2;0)
  HP_891(next_20_890,p) * HP_892(p,l)& l!=p --> H1(next_20_890,p);
 // POST (1;0)
  H1(l,p) & l=p --> G1(l,p);
 // POST (2;0)
  l::node<val_20_889,next_20_890>@M * G1(next_20_890,p)&l!=p --> G1(l,p)
 }

hpdefs [H1,G1][]:{
  G1(l_906,p_907) <-> emp&l_906=p_907
   or l_906::node<val_20_889,next_20_890>@M * G1(next_20_890,p_907)&
    l_906!=p_907;
  H1(l_904,p_905) <-> emp&l_904=p_905
   or H1(next_20_901,p_905) * l_904::node<val_20_900,next_20_901>@M&
    l_904!=p_905
 }
]

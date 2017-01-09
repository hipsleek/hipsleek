HeapPred HP_895(node a, node b).
HeapPred HP_894(node a, node b).

check_dll:SUCCESS[
ass [H1,G1][]:{
 // BIND (2;0)
  H1(l,prv)&l!=null --> l::node<prev_19_892,next_19_893>@M * HP_894(prev_19_892,prv) *HP_895(next_19_893,prv);
 // PRE_REC (2;0)
  HP_895(next_19_893,prv) |#| l::node<prev_19_892,next_19_893>@M --> H1(next_19_893,l);
 // POST (1;0)
  H1(l,prv)& l=null --> G1(l,prv);
 // POST (2;0)
  HP_894(prev_19_892,prv) * l::node<prv,next_19_893>@M *G1(next_19_893,l)& prev_19_892=prv --> G1(l,prv)
  }

hpdefs [H1,G1][]:{
 G1(l_950,prv_951) <->  emp&l_950=null
   or l_950::node<prv_951,next_19_893>@M * G1(next_19_893,l_950);
 H1(l_948,prv_949) <-> emp&l_948=null
   or H1(next_19_942,l_948) * l_948::node<prev_19_943,next_19_942>@M & prev_19_943=prv_949
 }
]
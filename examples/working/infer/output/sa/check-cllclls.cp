HeapPred HP_891(node a, node b).
HeapPred HP_892(node a, node b).
HeapPred HP_1322(node1 next_45_1320, node1@NI p).
HeapPred HP_1323(node1 p, node1@NI l).
HeapPred HP_1321(node dd_45_1319, node1@NI p).


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
  H1(l,p) <-> l::cll<p>@M;
 G1(l,p) <-> l::cll<p>@M
 }
]

check_csll_outer:SUCCESS[
ass [H2,G2][]:{
 // BIND (2;0)
 H2(l,p)&l!=p --> HP_1321(dd,p) * HP_1323(p,l) *l::node1<dd,next>@M * HP_1322(next,p);
 // PRE_REC (2;0)
 HP_1322(next,p) * HP_1323(p,l)&l!=p --> H2(next,p);
 // PRE (1;2;0)
 HP_1321(dd,p)&true --> dd::cll<dd>@M;
 // POST (1;0)
 H2(l,p)&l=p --> G2(l,p);
 // POST (1;1;2;0)
 G2(next,p) * l::node1<dd,next>@M * dd::cll<dd>@M&l!=p --> G2(l,p)
 }

hpdefs [H2,G2][]:{
 H2(l,p) <-> l::cll0<p>@M;
 G2(l,p) <-> l::cll0<p>
 }
]

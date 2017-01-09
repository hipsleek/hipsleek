HeapPred HP_891(node a, node b).
HeapPred HP_892(node a, node b).
HeapPred HP_1407(node1 next_55_1405, node1@NI p).
HeapPred HP_1408(node1 p, node1@NI l).
HeapPred HP_1406(node dd_55_1404, node1@NI p).
HeapPred HP_1778(node2 next_68_1775, node2@NI prv, node2@NI p).
HeapPred HP_1776(node1 dd_68_1773, node2@NI prv, node2@NI p).
HeapPred HP_1777(node2 prev_68_1774, node2@NI prv, node2@NI p).


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

check_csll_outer1:SUCCESS[
ass [H2,G2][]:{
 // BIND (2;0)
  H2(l,p)&l!=p --> HP_1406(dd,p) * HP_1408(p,l) * l::node1<dd,next>@M * HP_1407(next,p);
 // PRE_REC (2;0)
 HP_1407(next,p) * HP_1408(p,l)&l!=p --> H2(next,p);
 // PRE (1;2;0)
 HP_1406(dd,p)&true --> dd::cll<dd>@M;
 // POST (1;0)
 H2(l,p)&l=p --> G2(l,p);
 // POST (1;1;2;0)
  G2(next,p) * l::node1<dd,next>@M * dd::cll<dd>@M&l!=p --> G2(l,p)
 }

hpdefs [H2,G2][]:{
   H2(l,p) <-> l::csll<p>@M;
   G2(l,p) <-> l::csll<p>@M
 }
]

check_cdll_outer2:SUCCESS[
ass [H3,G3][]:{
 // BIND (2;0)
  H3(l,prv,p)&l!=p --> l::node2<dd,prev,next>@M *
  HP_1776(dd,prv,p) * HP_1777(prev,prv,p) * HP_1778(next,prv,p);
 // PRE_REC (2;0)
  HP_1778(next,prv,p)&l!=p |#| l::node2<dd,prev,next>@M& true
   --> H3(next,l,p);
 // PRE (1;1;2;0)
  HP_1776(dd,prev,p)&prev=prv --> dd::csll<dd>@M& true;
 // POST (1;0)
 H3(l,prv,p)&l=p --> G3(l,prv,p)& true;
 // POST (1;1;1;2;0)
 G3(next,l,p) * l::node2<dd,prev,next>@M * HP_1777(prev,prv,p) * dd::csll<dd>@M&l!=p &
   prev=prv --> G3(l,prev,p)
 }

hpdefs [H3,G3][]:{
 H3(l,prv,p) <-> l::cdll<prv,p>@M;
 G3(l,prv,p) <-> l::cdll<prv,p>
 }
]

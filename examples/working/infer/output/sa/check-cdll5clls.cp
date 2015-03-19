HeapPred HP_891(node a, node b).
HeapPred HP_892(node a, node b).
HeapPred HP_1459(node1 next_55_1452, node1@NI prv, node1@NI p).
HeapPred HP_1453(node dd1_55_1446, node1@NI prv, node1@NI p).
HeapPred HP_1454(node dd2_55_1447, node1@NI prv, node1@NI p).
HeapPred HP_1455(node dd3_55_1448, node1@NI prv, node1@NI p).
HeapPred HP_1456(node dd4_55_1449, node1@NI prv, node1@NI p).
HeapPred HP_1457(node dd5_55_1450, node1@NI prv, node1@NI p).
HeapPred HP_1458(node1 prev_55_1451, node1@NI prv, node1@NI p).


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

check_cdll_out1:SUCCESS[
ass [H2,G2][]:{
 // BIND (2;0)
 H2(l,prv,p)&l!=p --> l::node1<dd,dd1,dd2,dd3,dd4,prev,next>@M *
  HP_1453(dd,prv,p) * HP_1454(dd1,prv,p) * HP_1455(dd2,prv,p) * HP_1456(dd3,prv,p) *
  HP_1457(dd4,prv,p) * HP_1458(prev,prv,p) * HP_1459(next,prv,p);
 // PRE_REC (2;0)
 HP_1459(next,prv,p)& l!=p |#| l::node1<dd,dd1,dd2,dd3,dd4,prev,next>@M&
  true --> H2(next,l,p);
 // PRE (1;1;2;0)
 HP_1453(dd,prev,p)&prev=prv --> dd::cll<dd>@M;
 // PRE (1;1;1;2;0)
 HP_1454(dd,prev,p)&prev=prv --> dd::cll<dd>@M;
 // PRE (1;1;1;1;2;0)
 HP_1455(dd,prev,p)&prev=prv --> dd::cll<dd>@M;
 // PRE (1;1;1;1;1;2;0)
 HP_1456(dd,prev,p)&prev=prv --> dd::cll<dd>@M;
 // PRE (1;1;1;1;1;1;2;0)
 HP_1457(dd,prev,p)&prev=prv --> dd::cll<dd>@M;
 // POST (1;0)
 H2(l,prv,p)&l=p --> G2(l,prv,p);
 // POST (1;1;1;1;1;1;1;2;0)
  G2(next,l,p) * l::node1<dd,dd1,dd2,dd3,dd4,prev,next>@M * HP_1458(prev,prv,p) *
  dd::cll<dd>@M * dd1::cll<dd1>@M * dd2::cll<dd2>@M * dd3::cll<dd3>@M *
  dd4::cll<dd4>@M&l!=p & prev=prv --> G2(l,prev,p)
 }

hpdefs [H2,G2][]:{
 H2(l,prv,p) <-> l::cdll<prv,p>@M;
 G2(l,prv,p) <-> l::cdll<prv,p>@M
 }
]

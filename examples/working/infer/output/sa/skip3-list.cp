HeapPred HP_1104(node3 a, node3 b).
HeapPred HP_1105(node3 a, node3 b).
HeapPred HP_1106(node3 a, node3 b).
HeapPred HP_1392(node3 a, node3 b).
HeapPred HP_1393(node3 a, node3 b).
HeapPred HP_1394(node3 a, node3 b).
HeapPred HP_1405(node3 a, node3 b).
HeapPred HP_1793(node3 a).
HeapPred HP_1794(node3 a).
HeapPred HP_1795(node3 a).
HeapPred HP_1824(node3 a).

skip0:SUCCESS[
ass [H1][]:{
 // BIND (1;2;0)
  H1(l,e)&e!=l & l!=null --> l::node3<val,n,n1,n2>@M * HP_1104(n,e) * HP_1105(n1,e) * HP_1106(n2,e)& true;
 // PRE_REC (1;1;1;2;0)
  HP_1104(n,e)&true --> H1(n,e)& true;
 // POST (1;0)
  H1(l,e)&e=l --> emp& true;
 // POST (1;1;1;1;2;0)
  HP_1106(n,e)&n=null --> emp& true;
 // POST (1;1;1;1;2;0)
 HP_1105(n,e)&n=null --> emp&true
 }

hpdefs [H1][]:{
  H1(l,e) <-> l::lseg<e>
 }
]

skip1:SUCCESS[
ass [H2][]:{
// BIND (1;2;0)
 H2(l,e)&e!=l --> l::node3<val,n,n1,n2>@M * HP_1392(n,e) * HP_1393(n1,e) * HP_1394(n2,e)& true;
// PRE (1;2;0)
 HP_1392(n,e) * HP_1393(n1,e)&true --> n::lseg<n1>@M * HP_1405(n1,e)&true;
 // PRE_REC (1;1;1;2;0)
 HP_1405(n,e)&true --> H2(n,e)& true;
 // POST (1;0)
 H2(l,e)&e=l --> emp& true;
 // POST (1;1;1;1;2;0)
 HP_1394(n,e)&n=null --> emp&true
 }

hpdefs [H2][]:{
  H2(l,e) <-> l::skipll2<e>

 }
]

skip2:SUCCESS[
ass [H3][]:{
 // BIND (2;0)
  H3(l)&l!=null --> l::node3<val,n,n1,n2>@M * HP_1793(n) * HP_1794(n1) *
    HP_1795(n2)& true;
 // PRE_REC (2;0)
  HP_1795(n)&true --> H3(n)&true;
 // PRE (1;1;2;0)
  HP_1794(n1)&true |#| l::node3<val,n,n1,n2>@M& n=null --> n1::skipll2<n2>@M * HP_1824(n2)&true;
 // POST (1;0)
  H3(l)&l=null --> emp&true;
 // POST (1;1;1;2;0)
  HP_1793(n)&n=null --> emp& true
 }

hpdefs [H3][]:{
  H3(l) <-> l::skipll3<>

 }
]

HeapPred HP_1(node a).
HeapPred HP_596(node a).
HeapPred HP_2(node a, node b).

append[
ass []:{
  H1a(y) --> H1a(y);
 x::node<_,p> * G2(p,y) * H1a(y)& p!=null --> G2(x,y) * H1a(y);
 v_node_43_613=null --> H1a(y);
 H1a(y) * HP_596(p) * x::node<_,y>&p=null --> G2(x,y) * H1a(y);
 H1a(y) --> H1a(y);
 HP_596(p)& p!=null --> H1(p);
 H1(x) --> x::node<_,p> * HP_596(p)
 }

hpdefs [H1,H2,H1a,G1,G2]:{
 H1a(y) -->  true;
 G2(x,y) --> x::node<_,p> * HP_2(p,y);
 H1(x) -->  x::node<_,p>*HP_1(p);
 HP_2(x,p) --> x=p or x::node<_,p1> * HP_2(p1,p);
 HP_1(x) --> x=null or x::node<_,p1> * HP_1(p1)
 }
]


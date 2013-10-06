HeapPred HP_916(node a).
HeapPred HP_909(node a).

reverse:SUCCESS[
ass [H1,H2,G1][]:{
 // BIND (1;0)
  H1(x)&x!=null --> x::node<val_50_914,next_50_915>@M * HP_916(next_50_915);
 // PRE_REC (1;0)
  HP_916(next_50_915) --> H1(next_50_915);
 // PRE_REC (1;0)
  H2(y) * x_923::node<val_50_914,y>@M --> H2(x_923);
 // POST (1;0)
  G1(x',y') --> G1(x',y');
 // POST (2;0)
  H1(x) * H2(y')& x=null --> G1(x,y')
 }

hpdefs [H1,H2,G1][]:{
   G1(x_910,y_911) <-> H2(y_911)&x_910=null;
   HP_909(x_897) <-> htrue;
   H1(x_908) <-> emp&x_908=null
      or H1(next_50_906) * x_908::node<val_50_905,next_50_906>@M;
   H2(x_897) <-> H2(y) * x_897::node<val_50_888,y>@M or HP_909(x_897)
 }
]
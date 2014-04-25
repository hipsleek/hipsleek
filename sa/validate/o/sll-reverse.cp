HeapPred HP_916(node a).
HeapPred HP_909(node a).
HeapPred H1a(node a).

reverse:SUCCESS[
ass [H1,H2,G1][]:{
 // BIND (1;0)
  H1(x)&x!=null --> x::node<val_50_914,next_50_915>@M * HP_916(next_50_915);
 // PRE_REC (1;0)
  HP_916(next_50_915) --> H1(next_50_915);
 // PRE_REC (1;0)
  H2(y) * x_923::node<val_50_914,y>@M --> H2(x_923);
 // POST (1;0)
  G1(next,x',x,y')&x!=null --> G1(x,x',y,y');
 // POST (2;0)
  H1(x) * H2(y)& x=null & x'=null & x=x' & y=y' --> G1(x,x',y,y')
 }

hpdefs [H1,H2,G1][DP]:{
   G1(x,x',y,y') <-> H1a(y)& x=x' & y=y' & x=null & x'=null;
   H1(x_908) <-> emp&x_908=null
      or H1(next_50_906) * x_908::node<val_50_905,next_50_906>@M;
   H2(x_897) <-> H2(y) * x_897::node<val_50_888,y>@M or DP=x_897;
   H1a(y) <-> H2(y1) * y::node<val_50_888,y1>@M or DP=y
 }
]
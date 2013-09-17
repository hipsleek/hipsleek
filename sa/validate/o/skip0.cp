HeapPred HP_890(node a).
HeapPred HP_909(node a).
HeapPred HP_1b(node a).

skip0:SUCCESS[
ass [HX,HY,G1][]:{
   HX(x)&x!=null --> x::node<val_50_888,next_50_889>@M * HP_890(next_50_889),
 // PRE_REC
   HP_890(next_50_889) --> HX(next_50_889),
 // PRE_REC
 HY(y) * x_897::node<val_50_888,y> --> HY(x_897),
 // POST
 G1(x',y') --> G1(x',y'),
 // POST
  HX(x) * HY(y')& x=null --> G1(x,y')
 }

hpdefs [HX,HY,G1][]:{
   G1(x_910,y_911) <-> HY(y_911)&x_910=null,
   HP_909(x_897) <-> htrue,
   HX(x_908) <-> emp&x_908=null
      or HX(next_50_906) * x_908::node<val_50_905,next_50_906>@M,
   HY(x_897) <-> HY(y) * x_897::node<val_50_888,y>@M or HP_909(x_897)

 }
]
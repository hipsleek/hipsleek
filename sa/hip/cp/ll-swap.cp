HeapPred HP_1(node a).
HeapPred HP_538(node a).
HeapPred HP_584(node a).

swap:SUCCESS[
ass [H1,H2,H3,G1,G2,G3][]:{
 H1(x)&true --> x::node<val_117_521',next_117_522'> * HP_538(next_117_522');
 HP_538(t_21')&t_21'!=null --> H1(t_21');
 H3(z)&true --> H2(z)&true;
 H2(y)&true --> H3(y)&true;
 HP_538(next_119_550)&next_119_550=null --> emp&true;
 x'::node<val_117_543,y>@M& XPURE(H2(y)) --> G1(x')&true;
 H2(y)&true --> G2(y)&true;
 H3(z)&true --> G3(z)&true;
 G1(t_565) * x'::node<val_117_545,t_565>@M&true --> G1(x')&true;
 G3(y)&true --> G2(y)&true;
 G2(z)&true --> G3(z)&true
}

hpdefs [H1,H2,H3,G1,G2,G3][DLING_H2_z_595,DLING_H3_y_596]:{
  G1(x_583) --> x_583::node<val_117_543,y> * HP_584(y)&true;
  H1(x_589) --> x_589::node<_,next_117_522'> * HP_1(next_117_522');
  G2(y) --> emp&DLING_H2_z_595=y or emp&DLING_H3_y_596=y;
  H2(y) --> emp&DLING_H2_z_595=y or emp&DLING_H3_y_596=y;
  G3(y) --> emp&DLING_H2_z_595=y or emp&DLING_H3_y_596=y;
  H3(z) --> emp&DLING_H3_y_596=z or emp&DLING_H2_z_595=z;
  HP_584(y) --> emp&DLING_H3_y_596=y | DLING_H2_z_595=y
    or y::node<val_117_543,y_587>@M * HP_584(y_587)&true;
  HP_1(x) --> x =null or x::node<_,p> * HP_1(p)
 }
]

HeapPred HP_1(node a).
HeapPred HP_596(node a).
HeapPred HP_2(node a, node b).
HeapPred HP_649(node a).
HeapPred HP_643(node a, node b).

append:SUCCESS[
ass [H1,G2][]:{
 H1(x) --> x::node<_,p> * HP_596(p);
 HP_596(p)& p!=null --> H1(p);
 H1a(y) --> H1a(y);
 HP_596(p) & p=null --> emp&true;
 x::node<_,y> & XPURE(H1a(y)) --> G2(x,y);
 H1a(y) & H1a_y_615=y --> H1a(y);
 x::node<_,p> * G2(p,y) & XPURE(H1a(y)) & p!=null --> G2(x,y);
 H1a(y) & H1a_y_615=y --> H1a(y)

}


hpdefs [H1,G2][H1a_y_608]:{
 HP_649(next_43_543') -->
    emp&next_43_543'=null
    or next_43_543'::node<_,next_43_653> * HP_649(next_43_653)&true;
 HP_643(y_642_643,y_642) -->
   emp&y_642_643=y_642
   or y_642_643::node<val_43_603,y_642_647> * HP_643(y_642_647,y_642);
 H1a(y) --> emp&y=H1a_y_608;
 H1(x_649) --> x_649::node<val_43_542',next_43_543'> * HP_649(next_43_543')&true;
 G2(x_641,y_642) --> x_641::node<val_43_603,y_642_643> * HP_643(y_642_643,y_642)& y_642 =H1a_y_608
 }
]

/*
HP_649(next_43_543') -->
    emp&next_43_543'=null
    or next_43_543'::node<_,next_43_653> * HP_649(next_43_653)&true;
 HP_643(y_642_643,y_642) -->
   emp&y_642_643=y_642
   or y_642_643::node<val_43_603,y_642_647> * HP_643(y_642_647,y_642);
 H1a(y) --> emp&y=H1a_y_608;
 H1(x_649) --> x_649::node<val_43_542',next_43_543'> * HP_649(next_43_543')&true;
 G2(x_641,y_642) --> x_641::node<val_43_603,y_642_643> * HP_643(y_642_643,y_642)& y_642 =H1a_y_608
*/

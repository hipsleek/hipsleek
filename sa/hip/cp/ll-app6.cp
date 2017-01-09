HeapPred HP_1(node a).
HeapPred HP_539(node a).
HeapPred HP_581(node a, node b).

append:SUCCESS[
ass [H1,H2,G2][]:{
  H1(x)&true --> x::node<val_72_522',next_72_523'> * HP_539(next_72_523');
  HP_539(t_21')&t_21'!=null --> H1(t_21');
  H2(y)&true --> H2(y)&true;
  HP_539(next_74_551)&next_74_551=null --> emp&true;
  H2(y) * x'::node<val_72_544,y> --> G2(x',y)&true;
  G2(t_564,y) * x'::node<val_72_546,t_564>  --> G2(x',y)&true
}

hpdefs [H1,H2,G2][DLING_H2_y]:{
  G2(x_578,y_579) --> x_578::node<val_72_544,y_579_580> * HP_581(y_579_580,y_579) & DLING_H2_y=y_579;
  H1(x_587) --> x_587::node<val_72_522',next_72_523'> * HP_1(next_72_523');
  H2(y) --> emp&DLING_H2_y=y;
  HP_581(y_579_580,y_579) -->  emp&y_579=y_579_580
      or y_579_580::node<val_72_544,y_579_584> * HP_581(y_579_584,y_579);
  HP_1(x) --> x=null or x::node<_,p> * HP_1(p)
 }
]

HeapPred HP_1(node a).
HeapPred HP_545(node a, node b).
HeapPred HP_584(node a,node b).
HeapPred HP_594(node a).

append:SUCCESS[
ass [G1,G3][]:{
 G1(x,y)&true --> x::node<val_65_528',next_65_529'> *  HP_545(next_65_529',y);
 HP_545(t_22',y)&t_22'!=null --> G1(t_22',y)&true;
 HP_545(next_67_557,y) * x'::node<val_65_550,y> & x=x' &  next_67_557=null --> G3(x',x,y)&true;
 G3(t_570,t_567,y) * x'::node<val_65_552,t_570> & t_567!=null &  x=x' --> G3(x',x,y)
}

hpdefs [G1,G3][DLING_HP_571_y_601]:{
  G3(x_580,x_581,y_582) -->  x_580::node<val_65_550,y_582_583> * HP_584(y_582_583,y_582)&
     x_580=x_581 & DLING_HP_571_y_601=y_582;
  G1(x_592,y_593) --> x_592::node<val_65_528',next_65_529'> * HP_594(next_65_529')& DLING_HP_571_y_601=y_593;
  HP_584(y_582_583,y_582) --> emp&y_582=y_582_583
    or y_582_583::node<val_65_550,y_582_589> * HP_584(y_582_589,y_582);
  HP_594(next_65_529') --> emp&next_65_529'=null
    or next_65_529'::node<val_65_528',next_65_597> * HP_594(next_65_597)&true

 }
]

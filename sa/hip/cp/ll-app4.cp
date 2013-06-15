HeapPred HP_1(node a).
HeapPred HP_539(node a).
HeapPred HP_582(node a).

append:SUCCESS[
ass [H1,H2,H3,H4][]:{
 H1(x)&true --> x::node<val_68_522',next_68_523'> * HP_539(next_68_523')&true;
 HP_539(t_21')&t_21'!=null --> H1(t_21')&true;
 H2(y)&true --> H2(y)&true;
 HP_539(next_70_551)&next_70_551=null --> emp&true;
 x'::node<val_68_544,y> & XPURE(H2(y)) --> H3(x')&true;
 H2(y) --> H4(y)&true;
 H3(t_565) * x'::node<val_68_546,t_565>&true --> H3(x')&true;
 H4(y)&true --> H4(y)&true
}

hpdefs [H1,H2,H3,H4][H2_y_563]:{
 H3(x_581) --> x_581::node<val_68_544,y> * HP_582(y)&true;
 H1(x_587) --> x_587::node<val_68_522',next_68_523'> * HP_1(next_68_523');
 H2(y_593) --> emp&H2_y_563=y_593;
 H4(y_594) --> emp&H2_y_563=y_594;
 HP_1(x) --> x =null or x::node<_,p1> * HP_1(p1);
 HP_582(y) --> H2_y_563=y
    or y::node<val_68_544,y_585> * HP_582(y_585)&true

 }
]

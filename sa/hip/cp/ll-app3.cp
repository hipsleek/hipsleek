HeapPred HP_1(node a).
HeapPred HP_603(node a).
HeapPred HP_553(node a).

#append:SUCCESS[
ass [H1,H2,H3]:{
 H3(r_588) * x'::node<val_35_561,r_588>& v_node_35_576!=null --> H3(x');
 H2(y) * HP_553(v_node_35_570) * x'::node<val_35_559,y>&
  v_node_35_570=null --> H3(x')&true;
 H2(y)&true --> H2(y)&true;
 HP_553(v_node_35_576)& v_node_35_576!=null --> H1(v_node_35_576)&true;
 H1(x)&true --> x::node<val_35_533',next_35_534'> * HP_553(next_35_534')
}

hpdefs [H1,H2,H3]:{
 H1(x) --> x::node<_,p>*HP_1(p);
 HP_1(x) --> x=null or x::node<_,p1> * HP_1(p1);
 H2(y) --> emp&y=H2_y_615;
 H3(x_602) --> x_602::node<val_35_559,y> * HP_603(y);
 HP_603(y) --> emp&y=H2_y_615
    or y::node<val_35_559,y_606> * HP_603(y_606)&true
 }
]

HeapPred HP_1(node a).
HeapPred HP_603(node a).
HeapPred HP_553(node a).

append:SUCCESS[
ass [H1,H2,H3][]:{
 H1(x)&true --> x::node<_,p> * HP_553(p);
 HP_553(p)& p!=null --> H1(p)&true;
 H2(y)&true --> H2(y)&true;
 HP_553(v_node_35_570) & v_node_35_570=null --> emp&true;
 H2(y) * x'::node<val_35_559,y> --> H3(x')&true;
 H3(r_588) * x'::node<_,r_588> --> H3(x')
}

hpdefs [H1,H2,H3][]:{
 H1(x) --> x::node<_,p>*HP_1(p);
 HP_1(x) --> x=null or x::node<_,p1> * HP_1(p1);
 H2(y) --> emp&y=H2_y_615;
 H3(x_602) --> x_602::node<val_35_559,y> * HP_603(y);
 HP_603(y) --> emp&y=H2_y_615
    or y::node<val_35_559,y_606> * HP_603(y_606)&true
 }
]

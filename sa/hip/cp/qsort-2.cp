HeapPred HP_779(node a).
HeapPred HP_2(node a, node b).

 append_bll:SUCCESS[
ass [H4,H5,H6][]:{
  H4(x)&x!=null --> x::node<val_29_751',next_29_752'>@M *  (HP_779(next_29_752'));
 HP_779(v_node_29_753')&true --> H4(v_node_29_753');
 H5(y)&true --> H5(y)&true;
 H4(x)&x=null --> emp&true;
 H5(y)&res=y --> H6(y,res);
 res::node<val_29_786,xn_795>@M * (H6(y,xn_795))&true --> H6(y,res)
}

hpdefs [H4,H5,H6][DL_H5_y]:{
 H6(y,res) --> HP_2(y,res) & DL_H5_y=y;
 H4(x) -->  x=null or x::node<_,p1> * H4(p1);
 HP_2(y,p) --> p=y or p::node<_,p1> * HP_2(y,p1);
 H5(y) -->  y=DL_H5_y
 }
]

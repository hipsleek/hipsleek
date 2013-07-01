HeapPred HP_634(node a).
HeapPred HP_670(node a).

delete1:SUCCESS[
ass [H1,G2][]:{
 H1(x)&x!=null --> x::node<val_65_554',next_65_555'> * HP_634(next_65_555');
 HP_634(next_65_644)&true --> H1(next_65_644);
 H1(x)&x=null & v_node_63_553'=x --> emp&true;
 x=null & res=null --> G2(x,res);
 HP_634(next_65_642) * x::node<a,next_65_642> --> G2(x,next_65_642);
 x::node<v_int_65_656,next_65_644> * G2(next_65_644,v_node_66_672) *
     res::node<v_int_65_656,v_node_66_672> --> G2(x,res)
 }

hpdefs [H1,G2][]:{
  H1(a) --> a=null or a::node<_,p> * H1(p);
  G2(p,res_734) --> emp&res_734=null
     or G2(p1,v_node_66_708) * res_734::node<v_int_65_693,v_node_66_708>&true

 }
]

/*
 H1(a) --> a=null or a::node<_,p> * H1(p);
  G2(x_733,res_734) --> emp&res_734=null & x_733=null
     or x_733::node<a',res_734>&true
     or x_733::node<v_int_65_693,next_65_681> * G2(next_65_681,v_node_66_708) * 
    res_734::node<v_int_65_693,v_node_66_708>&true
*/

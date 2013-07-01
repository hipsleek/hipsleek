HeapPred HP_597(node a).
HeapPred HP_602(node a).

delete_mid:SUCCESS[
ass [H1,G2][]:{
  x::node<v_int_86_625,next_86_609> * G2(next_86_609,v_node_86_626) * 
  res::node<v_int_86_625,v_node_86_626>&
  true --> G2(x,res);
 HP_597(res) * x::node<val_85_620,res> --> G2(x,res);
 H1(x)&v_node_82_559'=x & x=null --> emp&true;
 x=null & res=null --> G2(x,res);
 HP_597(next_86_609)&true --> H1(next_86_609);
  H1(x)&x!=null --> x::node<val_85_568',next_85_569'> * HP_597(next_85_569')
 }

hpdefs [H1,G2][]:{
  H1(x) --> x=null or x::node<_,p> * H1(p);
  G2(_,res_696) -->
       res_696=null
   or  G2(_,v_node_86_668) * res_696::node<v_int_86_667,v_node_86_668>
 }
]

/*
H1(x) --> x=null or x::node<_,p> * H1(p);
  G2(x_695,res_696) -->
       res_696=null & x_695=null
   or  x_695::node<_,res_696>
   or  x_695::node<v_int_86_667,next_86_651> * G2(next_86_651,v_node_86_668) *
         res_696::node<v_int_86_667,v_node_86_668>
*/

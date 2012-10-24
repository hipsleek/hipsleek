HeapPred HP_2(node a, node b).
HeapPred HP_1(node a).

delete_list[
ass [D,E]:{
 D(x)&x=null --> E(x,v_564)&x=v_564;
 E(v_node_19_561,v_node_19_562) * x::node<val_19_555,v_node_19_561>&true --> E(x,x');
 HP_2(v_node_19_527',x)&x!=null --> D(v_node_19_527');
 D(x)&x!=null --> x::node<val_19_525',next_19_526'> * HP_2(next_19_526',x)

 }

hpdefs [D,E]:{
  E(x,v_594) --> emp&x=v_594 & x=null;
  D(x) --> x=null or x::node<_,p>*D(p)

 }
]

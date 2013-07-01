HeapPred HP_582(node b).
HeapPred HP_606(node a).
HeapPred HP_1(node a).
HeapPred HP_1a(node a).

delete_list:SUCCESS[
ass [D,E][]:{
   D(x)&x!=null --> x::node<_,next_19_533'> * HP_582(next_19_533');
   HP_582(v_node_19_534') --> D(v_node_19_534');
   D(x)&x=null --> emp & true;
   x=null & v_597 = null--> E(x,v_597);
   E(v_node_19_594,v_node_19_595) * x::node<_,v_node_19_594>&x'=null --> E(x,x')

 }

hpdefs [D,E][]:{
  E(x,v) -->  HP_1(x) * HP_1a(v);
  HP_1(x) --> x=null or x::node<_,p>*HP_1(p);
  HP_1a(x) --> x=null;
  D(x) --> x=null or x::node<_,p>*D(p)

 }
]

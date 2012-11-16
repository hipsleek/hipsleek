HeapPred HP_634(node a).
HeapPred HP_670(node a).

delete1:SUCCESS[
ass [H1,G2][]:{
 x::node<v_int_65_656,next_65_644> * G2(next_65_644,v_node_66_672) *
     v_node_66_567'::node<v_int_65_656,v_node_66_672> --> G2(x,v_node_66_567');
 HP_634(next_65_642) * x::node<a,next_65_642> --> G2(x,next_65_642);
 H1(x)&x=null & v_node_63_553'=null --> G2(x,v_node_63_553');
 HP_634(next_65_644)&true --> H1(next_65_644);
 H1(x)&x!=null --> x::node<val_65_554',next_65_555'> * HP_634(next_65_555')
 }

hpdefs [H1,G2][]:{
     H1(a) --> a=null or a::node<_,p> * H1(p);
     G2(x_682,v_node_63_683) -->
         emp&x_682=null & v_node_63_683=null
      or x_682::node<a',v_node_63_683>
      or x_682::node<v_int_65_656,next_65_644> * G2(next_65_644,v_node_66_672) * 
            v_node_63_683::node<v_int_65_656,v_node_66_672>&true
 }
]

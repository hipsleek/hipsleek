HeapPred HP_625(node next_96_565').
HeapPred HP_619(node y_617_618, node y_617).
HeapPred HP_613(node y).
HeapPred HP_631(node v_node_96_606).
HeapPred HP_583(node next_96_565', node x').
HeapPred HP_612(node a, node b).
HeapPred HP1(node a, node b).
HeapPred G3(node b, node c, node d).
HeapPred G1(node a).
HeapPred G2(node a, node b).
HeapPred H2(node a, node b).
HeapPred H1(node a).
HeapPred H(node a).

append[
ass [H1,G2]: {
 HP_583(v_node_96_600,x) * x::node<val_96_589,y>&v_node_96_600=null -->  G2(x,y)&true;
 H1(x)&true -->  x::node<val_96_564',next_96_565'> * HP_583(next_96_565',x)&true;
 HP_583(v_node_96_606,x)&v_node_96_606!=null -->  H1(v_node_96_606)&true;
 x::node<val_96_591,v_node_96_606> * G2(v_node_96_606,y)&v_node_96_606!=null -->  G2(x,y)&true
}
hpdefs [H1,G2]: {
 HP_631(v_node_96_615)&true -->  
 emp&v_node_96_615=null
 or HP_625(next_96_565')&true
 ;
 HP_619(y_617_618,y_617)&true -->  
 y_617_618::node<val_96_589,y_617_622> * HP_619(y_617_622,y_617)&true
 or emp&y_617_618=y_617
 ;
 HP_625(next_96_565')&true -->  
 next_96_565'::node<val_96_564',next_96_628> * HP_625(next_96_628)&true
 or emp&next_96_565'=null
 ;
 HP_613(y)&true -->  htrue&true;
 G2(x_616,y_617)&true -->  x_616::node<val_96_589,y_617_618> * HP_619(y_617_618,y_617)&
y_617=HP_613_y_630;
 H1(x_624)&true -->  x_624::node<val_96_564',next_96_565'> 
}
]


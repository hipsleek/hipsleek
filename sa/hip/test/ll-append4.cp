HeapPred HP_638(node next_93_560').
HeapPred HP_631(node y_629_630, node y_629).
HeapPred HP_608(node y).
HeapPred HP_578(node next_93_560').
HeapPred G3(node b, node c, node d).
HeapPred G1(node a).
HeapPred G2(node a, node b).
HeapPred H2(node a, node b).
HeapPred H1(node a).
HeapPred H(node a).

#append:SUCCESS[
ass [H1,G2]: {
 HP_578(v_node_93_595) * x::node<val_93_584,y>&v_node_93_595=null -->  G2(x,y)&true;
 H1(x)&true -->  x::node<val_93_559',next_93_560'> * HP_578(next_93_560')&true;
 HP_578(v_node_93_601)&v_node_93_601!=null -->  H1(v_node_93_601)&true;
 x::node<val_93_586,v_node_93_601> * G2(v_node_93_601,y)&v_node_93_601!=null -->  G2(x,y)&true
}
hpdefs [H1,G2]: {
 HP_631(y_629_630,y_629)&true -->  
 emp&y_629_630=y_629
 or y_629_630::node<val_93_584,y_629_634> * HP_631(y_629_634,y_629)&true
 ;
 HP_638(next_93_560')&true -->  
 emp&next_93_560'=null
 or next_93_560'::node<val_93_559',next_93_641> * HP_638(next_93_641)&true
 ;
 HP_578(v_node_93_636)&true -->  
 v_node_93_636::node<val_93_559',next_93_560'> * 
 next_93_560'::node<val_93_559',next_93_618>&next_93_618=null
 or v_node_93_636::node<val_93_559',next_93_560'> * 
    next_93_560'::node<val_93_559',next_93_619> * 
    next_93_619::node<val_93_559',next_93_620>&next_93_620=null
 or v_node_93_636::node<val_93_559',next_93_560'> * 
    next_93_560'::node<val_93_559',next_93_621> * 
    next_93_621::node<val_93_559',next_93_622>&next_93_622=null
 or v_node_93_636::node<val_93_559',next_93_623>&next_93_623=null
 or v_node_93_636::node<val_93_559',next_93_624> * 
    next_93_624::node<val_93_559',next_93_625>&next_93_625=null
 or v_node_93_636::node<val_93_559',next_93_626> * 
    next_93_626::node<val_93_559',next_93_627>&next_93_627=null
 or emp&v_node_93_636=null
 ;
 HP_608(y)&true -->  htrue&true;
 G2(x_628,y_629)&true -->  x_628::node<val_93_584,y_629_630> * HP_631(y_629_630,y_629)&
y_629=HP_608_y_643;
 H1(x_637)&true -->  x_637::node<val_93_559',next_93_560'> * HP_638(next_93_560')&true
}
]


HeapPred HP_632(node next_93_560').
HeapPred HP_626(node y_624_625, node y_624).
HeapPred HP_608(node y).
HeapPred HP_578(node next_93_560').
HeapPred G3(node b, node c, node d).
HeapPred G1(node a).
HeapPred G2(node a, node b).
HeapPred H2(node a, node b).
HeapPred H1(node a).
HeapPred H(node a).

append[
ass [H1,G2]: {
 HP_578(v_node_93_595) * x::node<val_93_584,y>&v_node_93_595=null -->  G2(x,y)&true;
 H1(x)&true -->  x::node<val_93_559',next_93_560'> * HP_578(next_93_560')&true;
 HP_578(v_node_93_601)&v_node_93_601!=null -->  H1(v_node_93_601)&true;
 x::node<val_93_586,v_node_93_601> * G2(v_node_93_601,y)&v_node_93_601!=null -->  G2(x,y)&true
}
hpdefs [H1,G2]: {
 HP_626(y_624_625,y_624)&true -->  
 emp&y_624_625=y_624
 or y_624_625::node<val_93_584,y_624_629> * HP_626(y_624_629,y_624)&true
 ;
 HP_632(next_93_560')&true -->  
 emp&next_93_560'=null
 or next_93_560'::node<val_93_559',next_93_635> * HP_632(next_93_635)&true
 ;
 HP_578(v_node_93_622)&true -->  
 v_node_93_622::node<val_93_559',next_93_612>&next_93_612=null
 or v_node_93_622::node<val_93_559',next_93_613> * 
    next_93_613::node<val_93_559',next_93_614>&next_93_614=null
 or v_node_93_622::node<val_93_559',next_93_615> * 
    next_93_615::node<val_93_559',next_93_616>&next_93_616=null
 or v_node_93_622::node<val_93_559',next_93_560'> * 
    next_93_560'::node<val_93_559',next_93_617>&next_93_617=null
 or v_node_93_622::node<val_93_559',next_93_560'> * 
    next_93_560'::node<val_93_559',next_93_618> * 
    next_93_618::node<val_93_559',next_93_619>&next_93_619=null
 or v_node_93_622::node<val_93_559',next_93_560'> * 
    next_93_560'::node<val_93_559',next_93_620> * 
    next_93_620::node<val_93_559',next_93_621>&next_93_621=null
 or emp&v_node_93_622=null
 ;
 HP_608(y)&true -->  htrue&true;
 G2(x_623,y_624)&true -->  x_623::node<val_93_584,y_624_625> * HP_626(y_624_625,y_624)&
y_624=HP_608_y_637;
 H1(x_631)&true -->  x_631::node<val_93_559',next_93_560'> * HP_632(next_93_560')&true
}
]


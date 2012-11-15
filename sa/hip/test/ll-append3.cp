HeapPred HP_719(node next_82_560').
HeapPred HP_713(node y_711_712, node y_711).
HeapPred HP_657(node next_82_560').
HeapPred HP_647(node next_97_540').
HeapPred HP_641(node y_639_640, node y_639).
HeapPred HP_585(node next_97_540').
HeapPred H1(node a).
HeapPred G1(node a, node b).

#append:SUCCESS[
ass [H1,G1]: {
 HP_657(v_node_82_674) * x::node<val_82_663,y>&v_node_82_674=null -->  G1(x,y)&true;
 H1(x)&true -->  x::node<val_82_559',next_82_560'> * HP_657(next_82_560')&true;
 HP_657(v_node_82_680)&v_node_82_680!=null -->  H1(v_node_82_680)&true;
 x::node<val_82_665,v_node_82_680> * G1(v_node_82_680,y)&y!=null & 
v_node_82_680!=null -->  G1(x,y)&true
}
hpdefs [H1,G1]: {
 HP_713(y_711_712,y_711)&true -->  
 emp&y_711_712=y_711
 or y_711_712::node<val_82_663,y_711_716> * HP_713(y_711_716,y_711)&true
 ;
 HP_719(next_82_560')&true -->  
 emp&next_82_560'=null
 or next_82_560'::node<val_82_559',next_82_722> * HP_719(next_82_722)&true
 ;
 HP_657(v_node_82_709)&true -->  
 v_node_82_709::node<val_82_559',next_82_560'> * 
 next_82_560'::node<val_82_559',next_82_699>&next_82_699=null
 or v_node_82_709::node<val_82_559',next_82_560'> * 
    next_82_560'::node<val_82_559',next_82_700> * 
    next_82_700::node<val_82_559',next_82_701>&next_82_701=null
 or v_node_82_709::node<val_82_559',next_82_560'> * 
    next_82_560'::node<val_82_559',next_82_702> * 
    next_82_702::node<val_82_559',next_82_703>&next_82_703=null
 or v_node_82_709::node<val_82_559',next_82_704>&next_82_704=null
 or v_node_82_709::node<val_82_559',next_82_705> * 
    next_82_705::node<val_82_559',next_82_706>&next_82_706=null
 or v_node_82_709::node<val_82_559',next_82_707> * 
    next_82_707::node<val_82_559',next_82_708>&next_82_708=null
 or emp&v_node_82_709=null
 ;
 G1(x_710,y_711)&true -->  x_710::node<val_82_663,y_711_712> * HP_713(y_711_712,y_711)&true;
 H1(x_718)&true -->  x_718::node<val_82_559',next_82_560'> * HP_719(next_82_560')&true
}
]


HeapPred HP_713(node y_711_712, node y_711).
HeapPred HP_65(node next_82_560').
HeapPred HP_647(node next_97_540').
HeapPred HP_641(node y_639_640, node y_639).
HeapPred HP_585(node next_97_540').
HeapPred H1(node a).
HeapPred G1(node a, node b).


#append2:SUCCESS[
ass [H1,G1]: {
 HP_657(v_node_82_674) * x::node<val_82_663,y>&v_node_82_674=null -->  G1(x,y)&true;
 H1(x)&true -->  x::node<val_82_559',next_82_560'> * HP_657(next_82_560')&true;
 HP_657(v_node_82_680)&v_node_82_680!=null -->  H1(v_node_82_680)&true;
 x::node<val_82_665,v_node_82_680> * G1(v_node_82_680,y)&y!=null & 
v_node_82_680!=null -->  G1(x,y)&true
}
hpdefs [H1,G1]: {
 HP_713(y_711_712,y_711)&true -->  
 emp&y_711_712=y_711
 or y_711_712::node<val_82_663,y_711_716> * HP_713(y_711_716,y_711)&true
 ;
 HP_719(next_82_560')&true -->  
 emp&next_82_560'=null
 or next_82_560'::node<val_82_559',next_82_722> * HP_719(next_82_722)&true
 ;
 HP_65(v_node_82_709)&true -->  
 v_node_82_709::node<val_82_559',next_82_560'> * 
 next_82_560'::node<val_82_559',next_82_699>&next_82_699=null
 or v_node_82_709::node<val_82_559',next_82_560'> * 
    next_82_560'::node<val_82_559',next_82_700> * 
    next_82_700::node<val_82_559',next_82_701>&next_82_701=null
 or v_node_82_709::node<val_82_559',next_82_560'> * 
    next_82_560'::node<val_82_559',next_82_702> * 
    next_82_702::node<val_82_559',next_82_703>&next_82_703=null
 or v_node_82_709::node<val_82_559',next_82_704>&next_82_704=null
 or v_node_82_709::node<val_82_559',next_82_705> * 
    next_82_705::node<val_82_559',next_82_706>&next_82_706=null
 or v_node_82_709::node<val_82_559',next_82_707> * 
    next_82_707::node<val_82_559',next_82_708>&next_82_708=null
 or emp&v_node_82_709=null
 ;
 G1(x_710,y_711)&true -->  x_710::node<val_82_663,y_711_712> * HP_713(y_711_712,y_711)&true;
 H1(x_718)&true -->  x_718::node<val_82_559',next_82_560'> * HP_719(next_82_560')&true
}
]

HeapPred HP_620(node next_82_535').
HeapPred HP_614(node y_612_613, node y_612).
HeapPred HP_558(node next_82_535').
HeapPred H1(node a).
HeapPred G1(node a, node b).

append[
ass [H1,G1]: {
 HP_558(v_node_82_575) * x::node<val_82_564,y>&v_node_82_575=null -->  G1(x,y)&true;
 H1(x)&true -->  x::node<val_82_534',next_82_535'> * HP_558(next_82_535')&true;
 HP_558(v_node_82_581)&v_node_82_581!=null -->  H1(v_node_82_581)&true;
 x::node<val_82_566,v_node_82_581> * G1(v_node_82_581,y)&y!=null & 
v_node_82_581!=null -->  G1(x,y)&true
}
hpdefs [H1,G1]: {
 HP_614(y_612_613,y_612)&true -->  
 emp&y_612_613=y_612
 or y_612_613::node<val_82_564,y_612_617> * HP_614(y_612_617,y_612)&true
 ;
 HP_620(next_82_535')&true -->  
 emp&next_82_535'=null
 or next_82_535'::node<val_82_534',next_82_623> * HP_620(next_82_623)&true
 ;
 HP_558(v_node_82_610)&true -->  
 v_node_82_610::node<val_82_534',next_82_600>&next_82_600=null
 or v_node_82_610::node<val_82_534',next_82_601> * 
    next_82_601::node<val_82_534',next_82_602>&next_82_602=null
 or v_node_82_610::node<val_82_534',next_82_603> * 
    next_82_603::node<val_82_534',next_82_604>&next_82_604=null
 or v_node_82_610::node<val_82_534',next_82_535'> * 
    next_82_535'::node<val_82_534',next_82_605>&next_82_605=null
 or v_node_82_610::node<val_82_534',next_82_535'> * 
    next_82_535'::node<val_82_534',next_82_606> * 
    next_82_606::node<val_82_534',next_82_607>&next_82_607=null
 or v_node_82_610::node<val_82_534',next_82_535'> * 
    next_82_535'::node<val_82_534',next_82_608> * 
    next_82_608::node<val_82_534',next_82_609>&next_82_609=null
 or emp&v_node_82_610=null
 ;
 G1(x_611,y_612)&true -->  x_611::node<val_82_564,y_612_613> * HP_614(y_612_613,y_612)&true;
 H1(x_619)&true -->  x_619::node<val_82_534',next_82_535'> * HP_558(next_82_535')&true
}
]


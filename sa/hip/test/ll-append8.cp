HeapPred HP_620(node next_50_619).
HeapPred HP_613(node y_612, node y).
HeapPred HP_581(node next_50_563', node x').
HeapPred HP1(node a, node b).
HeapPred H2(node a, node b).
HeapPred H1b(node a).
HeapPred H1a(node a).
HeapPred H1(node a).
HeapPred G3(node b, node c, node d).
HeapPred G1(node a).
HeapPred G2(node a, node b).

append[
ass [H1,H1a,G2]: {
 H1a(y) * HP_581(v_node_50_598,x) * x::node<val_50_587,y>&v_node_50_598=null -->  G2(x,y)&true;
 H1(x)&true -->  x::node<val_50_562',next_50_563'> * HP_581(next_50_563',x)&true;
 HP_581(v_node_50_604,x)&v_node_50_604!=null -->  H1(v_node_50_604)&true;
 H1a(y)&true -->  H1a(y)&true;
 x::node<val_50_589,v_node_50_604> * G2(v_node_50_604,y)&v_node_50_604!=null -->  G2(x,y)&true
}
hpdefs [H1,H1a,G2]: {
 HP_581(v_node_50_598)&true -->  
 v_node_50_598::node<val_50_618,next_50_619> * HP_620(next_50_619)&true
 or v_node_50_598::node<val_50_562',next_50_563'> * 
    next_50_563'::node<val_50_618,next_50_619> * HP_620(next_50_619)&true
 or emp&v_node_50_598=null
 ;
 G2(x,y)&true -->  x::node<val_50_611,y_612> * HP_613(y_612,y)&true;
 HP_613(y_612,y)&true -->  
 H1a(y)&y_612=y
 or y_612::node<val_50_611,y_616> * HP_613(y_616,y)&true
 ;
 H1(x)&true -->  x::node<val_50_618,next_50_619> * HP_620(next_50_619)&true;
 HP_620(next_50_619)&true -->  
 emp&next_50_619=null
 or next_50_619::node<val_50_618,next_50_623> * HP_620(next_50_623)&true
 ;
 H1a(y)&true -->  htrue&true
}
]


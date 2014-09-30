HeapPred HP_526(node a).
HeapPred HP_1(node a).


get_next:SUCCESS[
ass [H,G][]:{
   H(x)&true --> x::node<val_28_510',next_28_511'> * HP_526(next_28_511');
   x'::node<val_28_533,next_29_514'> &res=x' & next_29_514'=null --> G(x',res)
 }

hpdefs [H,G][DLING_HP_526_next_28_539]:{
   H(x) --> x::node<val_28_510',DLING_HP_526_next_28_539>;
   G(x_537,res_538) --> x_537::node<val_28_533,next_29_514'> &next_29_514'=null & res_538=x_537
 }
]

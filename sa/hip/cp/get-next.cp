HeapPred HP_526(node a).
HeapPred HP_1(node a).


get_next:SUCCESS[
ass [H,G][]:{
 H(x)&true --> x::node<val_31_510',next_31_511'> * HP_526(next_31_511');
 HP_526(res) * x'::node<val_31_533,next_32_514'> & next_32_514'=null --> G(x',res)&true

 }

hpdefs [H,G][DLING_HP_526_res_543]:{
 H(x) --> x::node<_,DLING_HP_526_res_543>;
 G(x,res) --> x::node<_,p> & p=null & DLING_HP_526_res_543=res
 }
]

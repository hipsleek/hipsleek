HeapPred HP_523(node a).
HeapPred HP_1(node a).


get_next:SUCCESS[
ass [H,G][]:{
   H(x)&true --> x::node<val_31_510',next_31_511'> * HP_523(next_31_511');
   HP_523(res) * x'::node<val_31_527,res> --> G(x',res)&true
 }

hpdefs [H,G][DLING_HP_523_res_533]:{
   H(x_530) --> x_530::node<val_31_510',DLING_HP_523_res_533>;
   G(x_531,res_532) --> x_531::node<val_31_527,res_532> & DLING_HP_523_res_533=res_532
 }
]

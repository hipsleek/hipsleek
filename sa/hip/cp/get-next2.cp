HeapPred HP_527(node a).
HeapPred HP_1(node a).


get_next:SUCCESS[
ass [H,G][]:{
 H(x)&true --> x::node<val_27_511',next_27_512'> * HP_527(next_27_512');
 HP_527(res) * x'::node<val_27_534,next_28_515'> & x=x' & next_28_515'=null --> G(x',x,res)&true
 }

hpdefs [H,G][DLING_HP_527_res_545]:{
  H(x) --> x::node<val_27_511',DLING_HP_527_res_545>;
  G(x,x_543,res_544) --> x::node<val_27_534,next_28_515'>@M&next_28_515'=null & x=x_543 &
   DLING_HP_527_res_545=res_544
 }
]

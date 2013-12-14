HeapPred HP_874(node a).
HeapPred HP_886(node a).
HeapPred HP_887(node a).

trav:SUCCESS[
ass [H,G][]:{
 // BIND (1;0)
  H(x)&x!=null --> x::node<next_21_873>@M * HP_874(next_21_873);
 // PRE_REC (1;0)
 HP_874(next_21_873) --> H(next_21_873);
 // POST (1;0)
 x::node<next_21_873>@M * G(next_21_873,x') --> G(x,x');
 // POST (2;0)
 H(x)&x=null & x'=null & x=x' --> G(x,x')
 }

hpdefs [H,G][]:{
 G(x_884,x_885) <-> HP_886(x_884) * HP_887(x_885);
 H(x_883) <->  emp&x_883=null or H(next_21_881) * x_883::node<next_21_881>@M;
 HP_886(self_tmp_infer_931) <-> emp&self_tmp_infer_931=null
    or HP_886(next_21_924) * self_tmp_infer_931::node<next_21_924>@M;
 HP_887(x_932) <-> emp&x_932=null
 }
]

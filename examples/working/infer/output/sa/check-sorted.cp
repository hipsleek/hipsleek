HeapPred HP_884(int a, int b).
HeapPred HP_885(node a, int b).

check_sorted:SUCCESS[
ass [H,G][]:{
 // BIND (2;0)
  H(x,v)&x!=null --> x::node<val_22_882,next_22_883>@M *
    HP_884(val_22_882,v) * HP_885(next_22_883,v);
 // PRE_REC (1;2;0)
  HP_885(next_22_883,v)& v<=t_30' |#| x::node<t_30',next_22_883>@M
   --> H(next_22_883,t_30');
 // POST(1;0)
  H(x,v)& x=null --> G(x,v);
 // POST (1;2;0)
  HP_884(val_22_882,v) * x::node<val_22_882,next_22_883>@M *
   G(next_22_883,val_22_882)& v<=val_22_882 --> G(x,v)
  }

hpdefs [H,G][]:{
 G(x_932,v_933) <-> emp&x_932=null
  or x_932::node<val_22_882,next_22_883>@M * G(next_22_883,val_22_882)&
    v_933<=val_22_882;
 H(x_930,v_931) <-> emp&x_930=null
  or H(next_22_923,val_22_924) * x_930::node<val_22_924,next_22_923>@M&
    v_931<=val_22_924

 }
]
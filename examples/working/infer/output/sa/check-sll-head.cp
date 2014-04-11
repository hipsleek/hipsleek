HeapPred HP_896(node a, node b).
HeapPred HP_897(node a, node b).
HeapPred HP_898(node a, node b).

foo:SUCCESS[
ass [H,G][]:{
 // BIND (2;0)
 H(x,h)&h!=x --> x::node<h_26_894,next_26_895>@M * HP_896(h_26_894,h) *
   HP_897(next_26_895,h) * HP_898(h,x);
 // PRE_REC (2;0)
 HP_897(next_26_895,h) * HP_898(h,x)& h!=x --> H(next_26_895,h);
 // POST (1;0)
 H(x,h)& h=x --> G(x,h);
 // POST (2;0)
 HP_896(h_26_894,h) * x::node<h,next_26_895>@M * G(next_26_895,h)&
   h!=x & h=h_26_894 --> G(x,h)
  }

hpdefs [H,G][]:{
  G(x_942,h_943) <-> emp&h_943=x_942
   or x_942::node<h_943,next_26_895>@M * G(next_26_895,h_943)&h_943!=x_942;
  H(x_940,h_941) <-> emp&h_941=x_940
   or H(next_26_934,h_941) * x_940::node<h_26_935,next_26_934>@M&
    h_26_935=h_941 & h_941!=x_940
 }
]
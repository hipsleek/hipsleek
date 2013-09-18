HeapPred HP_916(node a, node b).
HeapPred HP_917(node a, node b).

count_rest:SUCCESS[
ass [H,G][]:{
 // BIND (2;0)
  H(rest,h)&h!=rest --> rest::node<val_36_914,next_36_915>@M *
    HP_916(next_36_915,h) * HP_917(h,rest);
 // PRE_REC (2;0)
  HP_916(next_36_915,h) * HP_917(h,rest)& h!=rest --> H(next_36_915,h);
 // POST (1;0)
  H(rest,h) & h=rest --> G(rest,h);
 // POST (2;0)
  rest::node<val_36_914,next_36_915>@M * G(next_36_915,h)& h!=rest --> G(rest,h)
 }

hpdefs [H,G][]:{
 G(rest_937,h_938) <-> emp&h_938=rest_937
  or rest_937::node<val_36_914,next_36_915>@M * G(next_36_915,h_938) & h_938!=rest_937;
 H(rest_935,h_936) <-> emp&h_936=rest_935
  or H(next_36_932,h_936) * rest_935::node<val_36_931,next_36_932>@M&
    h_936!=rest_935
 }
]
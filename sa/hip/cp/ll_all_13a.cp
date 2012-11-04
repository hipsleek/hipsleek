HeapPred HP_616(node a,node b).
HeapPred HP_585(node a).
HeapPred HP_590(node a).

delete_mid[
ass [H1,G2]:{
   x::node<v_int_81_613,next_81_597> * G2(next_81_597,v_node_81_614) * v_node_81_566'::node<v_int_81_613,v_node_81_614>
      --> G2(x,v_node_81_566') * HP_616(v_node_81_614,v_node_81_566');
   HP_585(v_node_80_558') * x::node<val_80_608,v_node_80_558'>&true --> G2(x,v_node_80_558');
   H1(x)&x=null & v_node_77_555'=null --> G2(x,v_node_77_555');
   HP_590(next_81_597) --> H1(next_81_597);
   H1(x)&x!=null --> x::node<val_81_559',next_81_560'> *  HP_590(next_81_560')&true;
   H1(x)&x!=null --> x::node<val_80_556',next_80_557'> * HP_585(next_80_557')&true
 }

hpdefs [H1,G2]:{
     H1(x) --> x=null or x::node<_,p> * H1(p);
     G2(x_634,v_node_77_635) --> x_634::node<v_int_81_613,next_81_597> * G2(next_81_597,v_node_81_614) *
             v_node_77_635::node<v_int_81_613,v_node_81_614>&true
       or emp&x_634=null & v_node_77_635=null
 }
]

/*
G2(x1,v) --> x1::node<_,next_81_597> * G2(next_81_597,v_node_81_614)* v::node<_,v_node_81_614>
        or emp&x1=null & v=null
*/

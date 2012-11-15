HeapPred HP_1(node a).
HeapPred HP_580(node a).
HeapPred HP_2(node a, node b).

#append:SUCCESS[
ass [H1,G2]:{
    x::node<_,b> * G2(b,y')&b!=null & y=null & y'=null --> G2(x,y);
 	HP_580(a) * x::node<_,y'>&a=null & y=null & y'=null --> G2(x,y);
    HP_580(a)&a!=null --> H1(a);
    H1(x) --> x::node<_,p> * HP_580(p)
 }

hpdefs [H1,G2]:{H1(x) --> x::node<_,p>*HP_1(p);
   HP_1(x) --> x=null or x::node<_,p1> * HP_1(p1);
   G2(x,y) --> x::node<_,p> * HP_2(p,y) & y=null;
   HP_2(x,_) --> x=null or x::node<_,p1> * HP_2(p1,_)
 }
]


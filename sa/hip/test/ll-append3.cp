HeapPred HP1(node next).
HeapPred HP0(node y, node y0).
HeapPred HP(node next).

append:SUCCESS[
ass [H1,G1][]: {
 x::node<val,v> * G1(v,y)&y!=null & v!=null -->  G1(x,y)&true;
 HP(v)&v!=null -->  H1(v)&true;
 H1(x)&true -->  x::node<val,next> * HP(next)&true;
 HP(v) * x::node<val,y>&v=null -->  G1(x,y)&true
}
hpdefs [H1,G1][]: {
 H1(x)&true -->  x::node<val,next> * HP1(next)&true;
 G1(x,y0)&true -->  x::node<val,y> * HP0(y,y0)&true;
 HP(v)&true -->  
 v::node<val,next2> * next2::node<val,next>&next=null
 or v::node<val,next2> * next2::node<val,next0> * next0::node<val,next1>&
    next1=null
 or v::node<val,next2> * next2::node<val,next3> * next3::node<val,next4>&
    next4=null
 or v::node<val,next5>&next5=null
 or v::node<val,next6> * next6::node<val,next7>&next7=null
 or v::node<val,next8> * next8::node<val,next9>&next9=null
 or emp&v=null
 ;
 HP1(next)&true -->  
 emp&next=null
 or next::node<val,next0> * HP1(next0)&true
 ;
 HP0(y,y1)&true -->  
 emp&y=y1
 or y::node<val,y0> * HP0(y0,y1)&true
 
}
]


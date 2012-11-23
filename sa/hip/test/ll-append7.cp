HeapPred HP3(node next).
HeapPred HP2(node y).
HeapPred HP4(node y).
HeapPred HP0(node x).
HeapPred HP(node next).

append:SUCCESS[
ass [H1,G2][]: {
 x::node<val,v> * G2(v,y)&v!=null & y0=null & y=null -->  G2(x,y0)&true;
 HP(v)&v!=null -->  H1(v)&true;
 H1(x)&true -->  x::node<val,next> * HP(next)&true;
 HP(v) * x::node<val,y>&v=null & y0=null & y=null -->  G2(x,y0)&true
}
hpdefs [H1,G2][]: {
 G2(x,y0)&true -->  x::node<val,y> * HP2(y)&y0=null;
 H1(x)&true -->  x::node<val,next> * HP3(next)&true;
 HP4(y)&true -->  emp&y=null;
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
 HP3(next)&true -->  
 emp&next=null
 or next::node<val,next0> * HP3(next0)&true
 ;
 HP2(y)&true -->  
 emp&y=null
 or y::node<val,y0> * HP2(y0)&true
 ;
 HP0(x)&true -->  x::node<val,y> * HP2(y)&true
}
]


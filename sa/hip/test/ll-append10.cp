HeapPred HP2(node next).
HeapPred HP0(node y, node y0).
HeapPred HP(node next).

append:SUCCESS[
ass [H1,H1a,H1b,G2][]: {
 H1a(y)&true -->  H1b(y)&true;
 x::node<val,v> * G2(v,y) * H1b(y)&v!=null -->  G2(x,y) * H1b(y)&true;
 H1a(y)&true -->  H1a(y)&true;
 HP(v)&v!=null -->  H1(v)&true;
 H1(x)&true -->  x::node<val,next> * HP(next)&true;
 emp&v=null -->  H1b(y)&true;
 H1a(y) * HP(v) * x::node<val,y>&v=null -->  G2(x,y) * H1b(y)&true
}
hpdefs [H1,H1a,H1b,G2][]: {
 H1b(y)&true -->  emp&y=H1b0;
 H1a(y)&true -->  emp&y=H1b0;
 H1(x)&true -->  x::node<val,next> * HP2(next)&true;
 G2(x,y0)&true -->  x::node<val,y> * HP0(y,y0)&true;
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
 HP2(next)&true -->  
 emp&next=null
 or next::node<val,next0> * HP2(next0)&true
 ;
 HP0(y,y1)&true -->  
 emp&y=y1
 or y::node<val,y0> * HP0(y0,y1)&true
 
}
]


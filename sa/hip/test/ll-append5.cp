HeapPred HP2(node next).
HeapPred HP5(node y, node y0).
HeapPred HP7(node y).
HeapPred HP0(node x).
HeapPred HP3(node y).
HeapPred HP6(node v).
HeapPred HP(node next, node y).

append:SUCCESS[
ass [H2,G2][]: {
 x::node<val,v> * G2(v,y)&v!=null -->  G2(x,y)&true;
 HP(v,y)&v!=null -->  H2(v,y)&true;
 H2(x,y)&true -->  x::node<val,next> * HP(next,y)&true;
 HP(v,y) * x::node<val,y>&v=null -->  G2(x,y)&true
}
hpdefs [H2,G2][]: {
 H2(x,y)&true -->  x::node<val,next> * HP2(next)&y=HP4;
 G2(x,y0)&true -->  x::node<val,y> * HP5(y,y0)&y0=HP4;
 HP(v,y)&true -->  
 v::node<val,next2> * next2::node<val,next>&next=null & y=HP4
 or v::node<val,next2> * next2::node<val,next0> * next0::node<val,next1>&
    next1=null & y=HP4
 or v::node<val,next2> * next2::node<val,next3> * next3::node<val,next4>&
    next4=null & y=HP4
 or v::node<val,next5>&next5=null & y=HP4
 or v::node<val,next6> * next6::node<val,next7>&next7=null & y=HP4
 or v::node<val,next8> * next8::node<val,next9>&next9=null & y=HP4
 or emp&v=null & y=HP4
 ;
 HP7(y)&true -->  emp&y=HP4;
 HP6(v)&true -->  
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
 HP5(y,y1)&true -->  
 emp&y=y1
 or y::node<val,y0> * HP5(y0,y1)&true
 ;
 HP3(y)&true -->  emp&y=HP4;
 HP0(x)&true -->  x::node<val,next> * HP2(next)&true
}
]


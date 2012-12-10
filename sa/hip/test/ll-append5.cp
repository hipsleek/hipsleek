HeapPred HP0(node v1, node v0').
HeapPred HP2(node v1, node v0).
HeapPred HP3(node v0).
HeapPred HP(node v1, node v0').

append:SUCCESS[
ass [H2,G2][]: {
 x::node<val,v>@M * G2(v,y)&v!=null -->  G2(x,y)&true;
 HP(v,y)&v!=null -->  H2(v,y)&true;
 H2(x,y)&true -->  x::node<val,next>@M * HP(next,y)&true;
 HP(v,y) * x::node<val,y>@M&v=null -->  G2(x,y)&true
}
hpdefs [H2,G2][]: {
 H2(x,y)&true -->  x::node<val,next>@M * HP0(next,y)&DLING=y;
 G2(x,y0)&true -->  x::node<val,y>@M * HP2(y,y0)&DLING=y0;
 HP3(y)&true -->  emp&DLING=y;
 HP0(next,y)&true -->  
 emp&next=null
 or next::node<val,next0>@M * HP0(next0,y)&true
 ;
 HP2(y,y1)&true -->  
 emp&y=y1
 or y::node<val,y0>@M * HP2(y0,y1)&true
 ;
 HP(v,y)&true -->  
 HP0(next,y)&DLING=y
 or emp&v=null & DLING=y
 
}
]


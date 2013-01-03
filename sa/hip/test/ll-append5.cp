HeapPred HP0(node v1, node v0).
HeapPred HP2(node v0).
HeapPred HP(node v1, node v0').

append:SUCCESS[
ass [H2,G2][]: {
 x::node<val,v>@M * G2(v,y)&v!=null -->  G2(x,y)&true;
 HP(v,y)&v!=null -->  H2(v,y)&true;
 H2(x,y)&true -->  x::node<val,next>@M * HP(next,y)&true;
 HP(v,y) * x::node<val,y>@M&v=null -->  G2(x,y)&true
}
hpdefs [H2,G2][]: {
 G2(x,y0)&true -->  x::node<val,y>@M * HP0(y,y0)&true;
 H2(x,y)&true -->  x::node<val,next>@M * HP(next,y)&true;
 HP2(y)&true -->  emp&DLING=y;
 HP0(y0,y1)&true -->  
 y0::node<val,y>@M * HP0(y,y1)&true
 or emp&y0=y1
 ;
 HP(v,y)&true -->  
 v::node<val,next>@M * HP(next,y)&true
 or emp&v=null
 
}
]


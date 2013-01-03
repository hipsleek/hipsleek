HeapPred HP0(node v1, node v0).
HeapPred HP(node v0').

append:SUCCESS[
ass [H1,H1a,G2][]: {
 x::node<val,v>@M * G2(v,y)&v!=null -->  G2(x,y)&true;
 H1a(y)&true -->  H1a(y)&true;
 HP(v)&v!=null -->  H1(v)&true;
 H1(x)&true -->  x::node<val,next>@M * HP(next)&true;
 H1a(y) * x::node<val,y>@M&true -->  G2(x,y)&true;
 HP(v)&v=null -->  emp&true
}
hpdefs [H1,H1a,G2][]: {
 H1a(y)&true -->  emp&DLING=y;
 H1(x)&true -->  x::node<val,next>@M * HP(next)&true;
 G2(x,y0)&true -->  x::node<val,y>@M * HP0(y,y0)&true;
 HP(v)&true -->  
 v::node<val,next>@M * HP(next)&true
 or emp&v=null
 ;
 HP0(y,y1)&true -->  
 emp&y=y1 & DLING=y1
 or y::node<val,y0>@M * HP0(y0,y1)&true
 
}
]


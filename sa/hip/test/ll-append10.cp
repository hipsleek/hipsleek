HeapPred HP0(node v1, node v0).
HeapPred HP(node v0').

append:SUCCESS[
ass [H1,H1a,H1b,G2][]: {
 H1b(y)&true -->  H1b(y)&true;
 x::node<val,v>@M * G2(v,y)& XPURE(H1b(y)) & v!=null -->  G2(x,y)&true;
 H1a(y)&true -->  H1a(y)&true;
 HP(v)&v!=null -->  H1(v)&true;
 H1(x)&true -->  x::node<val,next>@M * HP(next)&true;
 H1a(y)&true -->  H1b(y)&true;
 x::node<val,y>@M& XPURE(H1a(y)) -->  G2(x,y)&true;
 HP(v)&v=null -->  emp&true
}
hpdefs [H1,H1a,H1b,G2][]: {
 H1b(y)&true -->  emp&DLING=y;
 H1a(y)&true -->  emp&DLING=y;
 G2(x,y0)&true -->  x::node<val,y>@M * HP0(y,y0)&DLING=y0;
 H1(x)&true -->  x::node<val,next>@M * HP(next)&true;
 HP0(y0,y1)&true -->  
 y0::node<val,y>@M * HP0(y,y1)&true
 or emp&y0=y1
 ;
 HP(v)&true -->  
 v::node<val,next>@M * HP(next)&true
 or emp&v=null
 
}
]


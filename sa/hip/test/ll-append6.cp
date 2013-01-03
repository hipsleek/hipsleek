HeapPred HP0(node v1, node v0).
HeapPred HP(node v0').

append:SUCCESS[
ass [H1,G2][]: {
 x::node<val,v>@M * G2(v,y) * y::node<a,flted>@M&v!=null & flted=null -->  G2(x,y)&true;
 HP(v)&v!=null -->  H1(v)&true;
 H1(x)&true -->  x::node<val,next>@M * HP(next)&true;
 y::node<a,flted>@M * x::node<val,y>@M&flted=null -->  G2(x,y)&true;
 HP(v)&v=null -->  emp&true
}
hpdefs [H1,G2][]: {
 G2(x,y0)&true -->  x::node<val,y>@M * y0::node<a,flted>@M * HP0(y,y0)&flted=null;
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


HeapPred HP(node v0').

get_next:SUCCESS[
ass [H,G][]: {
 HP(res) * x::node<val,next>@M&next=null -->  G(x,res)&true;
 H(x)&true -->  x::node<val,next>@M * HP(next)&true
}
hpdefs [H,G][]: {
 G(x,res)&true -->  x::node<val,next>@M&next=null & DLING=res;
 H(x)&true -->  x::node<val,DLING>@M&true;
 HP(res)&true -->  emp&DLING=res
}
]


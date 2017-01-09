HeapPred HP(node v0').

delete_list:SUCCESS[
ass [D,E][]: {
 emp&x0=null & x=null -->  E(x,x0)&true;
 D(x)&x=null -->  emp&true;
 x::node<val,v>@M&x0=null -->  E(x,x0)&true;
 HP(v)&true -->  D(v)&true;
 D(x)&x!=null -->  x::node<val,next>@M * HP(next)&true
}
hpdefs [D,E][]: {
 E(x,x0)&true -->  emp&x=null & x0=null;
 D(x)&true -->  
 emp&x=null
 or x::node<val,next>@M * D(next)&true
 ;
 HP(v)&true -->  D(v)&true
}
]


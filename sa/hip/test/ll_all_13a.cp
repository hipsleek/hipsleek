HeapPred HP0(node v0').
HeapPred HP(node v0').

delete_mid:SUCCESS[
ass [H1,G2][]: {
 x::node<v,next>@M * G2(next,v0) * res::node<v,v0>@M&true -->  G2(x,res)&true;
 HP0(next)&true -->  H1(next)&true;
 H1(x)&x!=null -->  x::node<val,next>@M * HP0(next)&true;
 HP(res) * x::node<val,res>@M&true -->  G2(x,res)&true;
 H1(x)&x!=null -->  x::node<val,next>@M * HP(next)&true;
 emp&x=null & res=null -->  G2(x,res)&true;
 H1(x)&v=x & x=null -->  emp&true
}
hpdefs [H1,G2][]: {
 G2(x,res)&true -->  
 emp&res=null & x=null
 or x::node<val,res>@M&true
 or x::node<v,next>@M * G2(next,v0) * res::node<v,v0>@M&true
 ;
 H1(x)&true -->  
 emp&x=null
 or x::node<val,next>@M * H1(next)&true
 ;
 HP(res)&true -->  G2(x,res)&true;
 HP0(next)&true -->  H1(next)&true
}
]


HeapPred HP(node v0').

delete1:SUCCESS[
ass [H1,G2][]: {
 x::node<v,next>@M * G2(next,v0) * res::node<v,v0>@M&true -->  G2(x,res)&true;
 HP(next)&true -->  H1(next)&true;
 H1(x)&x!=null -->  x::node<val,next>@M * HP(next)&true;
 HP(res) * x::node<a,res>@M&true -->  G2(x,res)&true;
 emp&x=null & res=null -->  G2(x,res)&true;
 H1(x)&v=x & x=null -->  emp&true
}
hpdefs [H1,G2][]: {
 H1(x)&true -->  
 x::node<val,next>@M * H1(next)&true
 or emp&x=null
 ;
 G2(x,res)&true -->  
 G2(next,v0) * res::node<v,v0>@M&true
 or emp&res=null
 ;
 HP(next)&true -->  H1(next)&true
}
]


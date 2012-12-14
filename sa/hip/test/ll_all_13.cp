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
 G2(x,res)&true -->  
 emp&res=null & x=null
 or x::node<a,res>@M&true
 or x::node<v,next>@M * G2(next,v0) * res::node<v,v0>@M&true
 ;
 H1(x)&true -->  
 emp&x=null
 or x::node<val,next>@M * H1(next)&true
 ;
 HP(res)&true -->  
 emp&res=null
 or res::node<v0,v>@M&v=null
 or res::node<v0,v1>@M&true
 or H1(res)&true
 
}
]


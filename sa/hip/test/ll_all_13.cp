HeapPred HP(node next).
HeapPred G3(node a, node b, node c).
HeapPred G2(node a, node b).
HeapPred G1(node a).
HeapPred G(node a, node b).
HeapPred H3(node a, node b, node c).
HeapPred H2(node a, node b).
HeapPred H1(node a).
HeapPred H(node a).

delete1:SUCCESS[
ass [H1,G2][]: {
 x::node<v,next> * G2(next,v0) * v1::node<v,v0>&true -->  G2(x,v1)&true;
 HP(next)&true -->  H1(next)&true;
 H1(x)&x!=null -->  x::node<val,next> * HP(next)&true;
 HP(next) * x::node<a,next>&true -->  G2(x,next)&true;
 H1(x)&x=null & res=null -->  G2(x,res)&true
}
hpdefs [H1,G2][]: {
 G2(x,res)&true -->  
 emp&res=null & x=null
 or x::node<a,res>&true
 or x::node<v,next> * G2(next,v0) * res::node<v,v0>&true
 ;
 H1(x)&true -->  
 emp&x=null
 or x::node<val,next> * H1(next)&true
 ;
 HP(next2)&true -->  
 emp&next2=null
 or next2::node<v2,v>&v=null
 or next2::node<v2,v0>&true
 or next2::node<val,next0>&next0=null
 or next2::node<val,next0> * next0::node<a,next0>&true
 or next2::node<val,next0> * next0::node<v2,next> * next0::node<v2,v1>&
    next=null
 or next2::node<val,next0> * next0::node<v2,next1> * next0::node<v2,v3> * 
    next1::node<a,v3>&true
 or H1(next2)&true
 
}
]



data node {
 int key;
 node left;
 node right;
}

HeapPred H(node a).
HeapPred G(node a).

tree<> == self=null
 or self::node<_,p,q>*p::tree<>*q::tree<>
inv true;

bool rand() 
 requires true
 ensures !res or res;

void foo(node x) 
/*
 requires x::tree<> 
 ensures x::tree<>;
*/
 infer [H,G] requires H(x)
 ensures G(x);

{
  if (x==null) return;
  else if (rand()) foo(x.left);
  else foo(x.right);
}

/*
# tree-conj-1.ss

post-pred G(..) not quite normalized

[ H(x_849) ::=  
 x_849::node<key_29_826,left_29_827,right_29_828>@M * H(left_29_827) * 
 H(right_29_828)&true
 or emp&x_849=null
 ,
 G(x_850) ::=  
 HP_801(right_29_799) * x_850::node<key_29_797,left_29_798,right_29_799>@M * 
 G(left_29_798)&true
 or HP_810(left_30_808) * 
    x_850::node<key_30_807,left_30_808,right_30_809>@M * G(right_30_809)&true
 or emp&x_850=null
 ,
 HP_801(right_29_799) ::

*/

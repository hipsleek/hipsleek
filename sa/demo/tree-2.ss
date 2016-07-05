
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

void foo(node x) 
/*
 requires x::tree<> & x!=null
 ensures x::tree<>;
*/

 infer [H,G] requires H(x)
 ensures G(x);

{
  if (x.left==null) return;
  if (x.right==null) return;
  foo(x.left);
  foo(x.right);
}

/*
# tree.ss

GOT BELOW which seems wrong!

 H(x_971) ::=  x_971::node<key_25_797,left_25_798,right_25_799>@M * HP_801(right_25_799)&
left_25_798=null,
 G(x_973) ::=  x_973::node<key_25_797,left_25_798,right_25_799>@M * 
HP_974(left_25_798,right_25_799)&true,
 HP_801(right_25_870) ::=  
 right_25_870::node<key_25_797,left_25_798,right_25_799>@M * 
 HP_800(left_25_798) * HP_801(right_25_799)&true
 or emp&right_25_870=null
 ,
 HP_974(left_25_798,right_25_799) ::=  
 emp&left_25_798=null
 or emp&right_25_799=null & left_25_798!=null
 or left_25_798::node<key_25_797,left_25_975,right_25_976>@M * 
    HP_974(left_25_975,right_25_976) * 
    right_25_799::node<key_25_797,left_25_975,right_25_976>@M * 
    HP_974(left_25_975,right_25_976)&true
 ,
 HP_800(left_25_972) ::=  emp&left_25_972=null]

*/


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

 requires x::node<_,l,r> * l::tree<> * r::tree<> 
 ensures x::node<_,l,r> * l::tree<> * r::tree<>;

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

GOT BELOW which is WRONG
========================
[ H(x_971) ::=  x_971::node<key_31_797,left_31_798,right_31_799>@M * HP_801(right_31_799)&
left_31_798=null,
 G(x_973) ::=  x_973::node<key_31_797,left_31_798,right_31_799>@M * 
HP_974(left_31_798,right_31_799)&true,
 HP_801(right_31_870) ::=  
 right_31_870::node<key_31_797,left_31_798,right_31_799>@M * 
 HP_800(left_31_798) * HP_801(right_31_799)&true
 or emp&right_31_870=null
 ,
 HP_974(left_31_798,right_31_799) ::=  
 emp&left_31_798=null
 or emp&right_31_799=null & left_31_798!=null
 or left_31_798::node<key_31_797,left_31_975,right_31_976>@M * 
    HP_974(left_31_975,right_31_976) * 
    right_31_799::node<key_31_797,left_31_975,right_31_976>@M * 
    HP_974(left_31_975,right_31_976)&true
 ,
 HP_800(left_31_972) ::=  emp&left_31_972=null]




POSSIBLE ALGO
=============


[ H(x)&true --> x::node<key_25_797,left_25_798,right_25_799>@M * 
       HP_800(left_25_798) * HP_801(right_25_799)&true,

 HP_800(left_25_798)&left_25_798!=null --> H(left_25_798)&true,

 HP_801(right_25_799)&right_25_799!=null --> H(right_25_799)&true,

 HP_801(right_25_799)&right_25_799=null --> emp&true,

 HP_800(left_25_798)&left_25_798=null --> emp&true,

 HP_800(left_25_798)&left_25_798=null --> emp&true,

========

 HP_800(left_25_798) * x::node<key_25_797,left_25_798,right_25_799>@M&
  left_25_798!=null & right_25_799=null --> G(x)&true,

 HP_801(right_25_799) * x::node<key_25_797,left_25_798,right_25_799>@M&
  left_25_798=null --> G(x)&true,

 HP_801(right_25_799) * x::node<key_25_797,left_25_798,right_25_799>@M&
  left_25_798=null --> G(x)&true,

 x::node<key_25_797,left_25_798,right_25_799>@M * G(left_25_798) * 
  G(right_25_799)&left_25_798!=null & right_25_799!=null --> G(x)&true]



[ 
 H(x_933) ::=  x_933::node<key_25_797,left_25_798,right_25_799>@M * 
  HP_934(left_25_798,right_25_799) * HP_801(right_25_799)&true,

 G(x_936) ::=  x_936::node<key_25_797,left_25_798,right_25_799>@M * 
  HP_937(left_25_798,right_25_799)&true,

 HP_934(left_25_798,right_25_799) ::=  emp&left_25_798=null,

 HP_801(right_25_799) ::=  
 right_25_799::node<key_25_797,left_25_798,right_25_799>@M * 
 HP_800(left_25_798) * HP_801(right_25_799)&true
 or H(right_25_799)&right_25_799!=null
 or emp&right_25_799=null


 HP_937(left_25_798,right_25_799) ::=  
 emp&left_25_798=null
 or emp&right_25_799=null & left_25_798!=null
 or left_25_798::node<key_25_797,left_25_938,right_25_939>@M * 
    HP_937(left_25_938,right_25_939) * 
    right_25_799::node<key_25_797,left_25_938,right_25_939>@M * 
    HP_937(left_25_938,right_25_939)&true
 ,

 HP_800(left_25_935) ::=  
 emp&left_25_935=null
 or emp&left_25_935!=null
 ]


============================================

[ H(x)&true <--> x::node<key_25_797,left,right>@M * 
       HP_800(left) * HP_801(right)&true,

 HP_800(left)&left!=null --> 
   //H(left)&true,
    left::node<key_25_797,left,right>@M * 
       HP_800(left) * HP_801(right)&true,


 HP_800(left)&left=null --> emp&true,

 HP_801(right)&right!=null --> 
    right::node<key_25_797,left,right>@M * 
       HP_800(left) * HP_801(right)&true,

 HP_801(right)&right=null --> emp&true,

 HP_801(x) --> x=null
    or  x::node<key_25_797,left,right>@M * 
       HP_800(left) * HP_801(right)& x!=null 

 HP_800(x) --> x=null
    or  x::node<key_25_797,left,right>@M * 
       HP_800(left) * HP_801(right)& x!=null 

 HP_800(x) <--> HP_801(x) ????

================================

[ H(x)&true <--> x::node<key_25_797,left,right>@M * 
       HP_800(left) * HP_800(right)&true,

 HP_800(x) --> x=null
    or  x::node<key_25_797,l,r>@M * 
       HP_800(l) * HP_800(r)& x!=null 


=================================


 HP_800(left) * x::node<key_25_797,left,right>@M&
  left!=null & right=null --> G(x)&true,

 HP_800(right) * x::node<key_25_797,left,right>@M&
  left=null --> G(x)&true,

 x::node<key_25_797,left,right>@M * G(left) * 
  G(right)&left!=null & right!=null --> G(x)&true]



===>

  x::node<k,l,r> * G1(l) * G2(r) --> G(x)

===>

  x::node<k,l,r> * G1(l) * G2(r) <--> G(x)

  left::node<key_25_797,l,r>@M * 
       HP_800(l) * HP_800(r)& x!=null 
  or left=null 
  or left::node<k,l,r> * G1(l) * G2(r) 
    <--> G1(left)

  right::node<key_25_797,l,r>@M * 
       HP_800(l) * HP_800(r)& x!=null 
  or right=null 
  or right::node<k,l,r> * G1(l) * G2(r)
    <--> G2(right)

====>
 G1=G2

====>

  x::node<k,l,r> * G1(l) * G1(r) <--> G(x)

  left::node<key_25_797,l,r>@M * 
       HP_800(l) * HP_800(r)& x!=null 
  or left=null 
  or left::node<k,l,r> * G1(l) * G1(r) 
    <--> G1(left)

====>
 G1=HP_800
====>
  left::node<key_25_797,l,r>@M * 
       HP_800(l) * HP_800(r)& x!=null 
  or left=null 
    <--> G1(left)
====>
   HP_800(left) <--> G1(left)


====>

  G1=G2

====>

  x::node<k,l,r> * G1(l) * G1(r) <--> G(x)

  H_800(left) & left!=null 
  or left=null 
  or G(left)&left!=null <--> G1(left)

====>


  left::node<key_25_797,l,r>@M * HP_801(l) * HP_800(r)
  or left=null 
  or left::node<k,l,r> * G1(l) * G2(r) <--> G1(left)

  right::node<key_25_797,l,r>@M * HP_800(l) * HP_801(r)
  or right=null 
  or right::node<k,l,r> * G1(l) * G2(r) <--> G2(right)

====>

  G1(l) <-> HP_801(l)
  G2(l) <-> HP_800(l)

  left=null 
  or left::node<k,l,r> * G1(l) * G2(r) <--> G1(left)

  G1(l) <-> HP_800(l)
  G2(l) <-> HP_801(l)

  left=null 
  or left::node<k,l,r> * G1(l) * G2(r) <--> G2(left)

  G1=G2=HP_801=HP_800


  left=null 
  or left::node<k,l,r> * G1(l) * G1(r) <--> G1(left)

====>

[ H(x)&true <--> x::node<key_25_797,left,right>@M * 
       HP_800(left) * HP_800(right)&true,

  HP_800(x) --> x=null
    or  x::node<key_25_797,l,r>@M * 
       HP_800(l) * HP_800(r)& x!=null 

  G(x) <-> x::node<k,l,r> * HP_800(l) * HP_800(r)


*/



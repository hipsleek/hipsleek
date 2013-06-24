
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
  if (x.right==null) return;
  foo(x.right);
}

/*
# tree-3.ss


 H(x)&true --> x::node<_,left,right>@M * 
  HP_1(left) * HP_2(right)&true,

 HP_2(right)&right!=null --> H(right)&true,

 HP_2(right)&right=null --> emp&true,

=====

 HP_1(left) * x::node<_,left,right>@M&
  right=null --> G(x)&true,
 HP_1(left) * x::node<_,left,right>@M * 
  G(right)&right!=null --> G(x)&true]

======>
 HP_1 is UNKNOWN

 H(x)&true <--> x::node<_,left,right>@M * 
    HP_1(left) * HP_2(right)&true,

 HP_2(x)&x!=null --> 
     x::node<_,left,right>@M * 
      HP_1(left) * HP_2(right)&true,

 HP_2(x)&x=null --> emp&true,

====>
 HP_2(x) --> x=null
   or x::node<_,left,right>@M * 
      HP_1(left) * HP_2(right)&true,

====>
 HP_2(x) <--> x=null
   or x::node<_,left,right>@M * 
      HP_1(left) * HP_2(right)&true,

======
 HP_1(left) * x::node<_,left,null>@M&  --> G(x)&true,
 HP_1(left) * x::node<_,left,right>@M * 
  G(right)&right!=null --> G(x)&true]

=====>
 HP_1(left) * x::node<_,left,right>@M * G1(right)  --> G(x)&true,
 
 right=null or  G(right)&right!=null --> G1(right)
=====>
 G(x) <--> HP_1(left) * x::node<_,left,right>@M * G1(right)  

=====>
 right=null or  HP_1(l) * right::node<_,l,r>@M * G1(r)
     --> G1(right)

=============
 H(x)&true <--> x::node<_,left,right>@M * 
    HP_1(left) * HP_2(right)&true,
 HP_2(x) <--> x=null
   or x::node<_,left,right>@M * 
      HP_1(left) * HP_2(right)&true,
 G(x) <--> HP_1(left) * x::node<_,left,right>@M * G1(right)  
 G1(right) <-->
      right=null or  HP_1(l) * right::node<_,l,r>@M * G1(r)

 
*/



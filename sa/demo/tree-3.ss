
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


=====================
# tree-3.ss

GOT

The first parameter of below seems useless. Can we avoid introducing it?

 HP_833(left_30_789,right_30_790) ::=  

or do we need to try --sa-useless?

==========

[ H(x_831) ::=  x_831::node<key_30_788,left_30_789,right_30_790>@M * HP_791(left_30_789) * 
                HP_792(right_30_790)&true,
 G(x_832) ::=  x_832::node<key_30_788,left_30_789,right_30_790>@M * 
                HP_833(left_30_789,right_30_790) * HP_791(left_30_789)&true,

 HP_792(right_30_830) ::=  
 emp&right_30_830=null
 or right_30_830::node<key_30_788,left_30_789,right_30_790>@M * 
    HP_791(left_30_789) * HP_792(right_30_790)&true
 ,

 HP_833(left_30_789,right_30_790) ::=  
 emp&right_30_790=null
 or right_30_790::node<key_30_788,left_30_834,right_30_835>@M * 
    HP_833(left_30_834,right_30_835) * HP_791(left_30_834)&true
 ,
 HP_791(left_30_789) ::= NONE]

*/



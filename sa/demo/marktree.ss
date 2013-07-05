data node {
 int val;
 node left;
 node right;
}

HeapPred H(node a).
HeapPred G(node a,int x).

tree<v> == self=null
 or self::node<0,p,q> * p::tree<0> * q::tree<0> & v = 0
 or self::node<0,p,q> * p::tree<_> * q::tree<_> & v = 1 
 or self::node<1,p,q> * p::tree<1> * q::tree<1> & v = 2
 inv true;

/*
treeG<> == self=null
 or self::node<0,p,q> * p::tree<0> * q::tree<0> & v = 0
 or self::node<0,p,q> * p::tree<_> * q::tree<_> & v = 1 
 or self::node<1,p,q> * p::treeG<> * q::treeG<> & v = 2
 inv true;
*/

void mark(node x) 
/*
 requires x::tree<_>
 ensures x::tree<2>;
*/
 infer [H,G] 
 requires H(x)
 ensures G(x,_);
{
node l,r;
if(x == null) return;
else {
  int ttt=x.val;
 if (ttt == 1) return;
 //assert ttt'=0; //' pure property not inferred.
 l = x.left;
 r = x.right;
 x.val = 1;
 mark(l);
 mark(r);
 }
}

/*
[ H(x)&x=null --> G(x,Anon_1008),
 HP_975(left_36_973) * HP_976(right_36_974) * 
  x::node<val_36_972,left_36_973,right_36_974>@M&
  val_36_972=1 --> G(x,Anon_1007),
 H(x)&x!=null --> x::node<val_36_972,left_36_973,right_36_974>@M * 
  HP_975(left_36_973) * HP_976(right_36_974),
 HP_975(left_36_973) --> H(left_36_973),
 HP_976(right_36_974) --> H(right_36_974),

 x::node<v_int_41_1000,left_36_973,right_36_974>@M * 
  G(left_36_973,Anon_1005) * G(right_36_974,Anon_1010)&
  v_int_41_1000=1 --> G(x,Anon_1011)]

=======

 H(x_1012) ::= x_1012::node<val_36_972,left_36_973,right_36_974>@M 
      * HP_975(left_36_973) * HP_976(right_36_974)
   \/  x_1012::node<val_36_972,left_36_973,right_36_974>@M 
       * H(left_36_973) * H(right_36_974)
   \/  emp&x_1012=null,

 G(x_1013,Anon_1014) ::= HP_975(left_36_973) * HP_976(right_36_974) * 
x_1013::node<val_36_972,left_36_973,right_36_974>@M&val_36_972=1
   \/  x_1013::node<v_int_41_1000,left_36_973,right_36_974>@M * 
G(left_36_973,Anon_1005) * G(right_36_974,Anon_1010)&v_int_41_1000=1
   \/  emp&x_1013=null]

*/

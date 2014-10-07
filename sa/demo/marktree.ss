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
 assert ttt'=0; //' need to pick up inferred from assertion ...
 l = x.left;
 r = x.right;
 x.val = 1;
 mark(l);
 mark(r);
 }
}

/*
# marktree

hprel_ass: [ HP_975(val_36_972) --> emp&val_36_972=0]

Not picked in:

[ H(x)&x=null --> G(x,Anon_1009),
 HP_975(val_36_972@NI) * HP_976(left_36_973) * HP_977(right_36_974) * 
  x::node<val_36_972,left_36_973,right_36_974>@M&
  val_36_972=1 --> G(x,Anon_1008),
 H(x)&x!=null --> x::node<val_36_972,left_36_973,right_36_974>@M * 
  HP_975(val_36_972@NI) * HP_976(left_36_973) * HP_977(right_36_974),
 HP_976(left_36_973) --> H(left_36_973),
 HP_977(right_36_974) --> H(right_36_974),
 HP_975(val_36_972@NI) * x::node<v_int_41_1001,left_36_973,right_36_974>@M * 
  G(left_36_973,Anon_1006) * G(right_36_974,Anon_1011)&val_36_972!=1 & 
  v_int_41_1001=1 --> G(x,Anon_1012)]


*/

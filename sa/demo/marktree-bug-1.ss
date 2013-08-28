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
 assert ttt'=0 assume ttt'=0; //' pure property not inferred.
 l = x.left;
 r = x.right;
 x.val = 1;
 mark(l);
 mark(r);
 }
}

/*
# marktree-bug-1 

assert/assume losing a lot of info, such as x=x' 

 id: 9; caller: []; line: 38; classic: false; kind: ASSERT/ASSUME; hec_num: 2; evars: []; infer_vars: [H,G,HP_976,HP_977,HP_978]; c_heap: emp
 checkentail HP_976(val_36_973) * HP_977(left_36_974) * HP_978(right_36_975) * 
x::node<val_36_973,left_36_974,right_36_975>@M[Orig]&x=x' & x'!=null & 
!(v_bool_34_948') & x'!=null & !(v_bool_34_948') & ttt_49'=val_36_973 & 
ttt_49'!=1 & !(v_bool_37_931') & ttt_49'!=1 & !(v_bool_37_931')&
{FLOW,(22,23)=__norm}[]
 |-  emp&ttt_49'=0&{FLOW,(22,23)=__norm}[]. 
hprel_ass: [ HP_976(val_36_973) --> emp&val_36_973=0]
res:  [
  HP_976(val_36_973) * HP_977(left_36_974) * HP_978(right_36_975) * x::node<val_36_973,left_36_974,right_36_975>@M[Orig]&ttt_49'=0 & val_36_973=0&{FLOW,(22,23)=__norm}[]
  ]


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

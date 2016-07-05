
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
  foo(x.left);
}

/*
# tree.ss


[ H(x_809) ::=  x_809::node<key_25_788,left_25_789,right_25_790>@M 
    * HP_791(left_25_789) * HP_792(right_25_790)&true,

 G(x_810) ::= HP_792(right_25_790) * x_810::node<key_25_788,left_25_789,right_25_790>@M&
                left_25_789=null
 or HP_792(right_25_790) * 
    x_810::node<key_25_788,left_25_789,right_25_790>@M * G(left_25_789)&
    left_25_789!=null
 ,

 HP_791(left_25_804) ::=  
 emp&left_25_804=null
 or left_25_804::node<key_25_788,left_25_789,right_25_790>@M * 
    HP_791(left_25_789) * HP_792(right_25_790)&true
 ,

 HP_792(right_25_790) ::= NONE]



 State:
x'::node<Anon_821,p_822,q_823>@M[Orig] * p_822::tree@M[0][Orig] 
* q_823::node<Anon_824,Anon_825,Anon_826>@M[Orig]&x=x' 
& x!=null & p_822!=null & !(v_bool_27_783') & p_822!=null 
& !(v_bool_27_783') & q_823!=null & !(v_bool_30_782') & q_823!=null & !(v_bool_30_782')

Why are not two Anons?

*/

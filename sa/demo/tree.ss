
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

 State:
x'::node<Anon_821,p_822,q_823>@M[Orig] * p_822::tree@M[0][Orig] 
* q_823::node<Anon_824,Anon_825,Anon_826>@M[Orig]&x=x' 
& x!=null & p_822!=null & !(v_bool_27_783') & p_822!=null 
& !(v_bool_27_783') & q_823!=null & !(v_bool_30_782') & q_823!=null & !(v_bool_30_782')

Why are not two Anons?

*/

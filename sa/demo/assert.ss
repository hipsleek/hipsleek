data node {
 int val;
 node left;
 node right;
}

HeapPred H(node x).
PostPred G(node x).

void mark(node x) 
/*
 requires x::node<1,b,c> 
 ensures x::node<1,b,c>;
*/
 infer [H,G]
 requires H(x)
 ensures G(x);
{
  node ttt= x.right;
  dprint;
  assert ttt'=null assume ttt'=null;
  dprint;
}

/*
# assert.ss

 Why is x'=x information lost? This seem to occur for
 inference but not verification.

Successful States:
[
 Label: 
 State:HP_910(left_19_908) * HP_911(right_19_909) * x::node<val_19_907,left_19_908,right_19_909>@M[Orig]&x=x' & right_19_909=ttt_30'&{FLOW,(22,23)=__norm}[]
       es_var_measures 2: MayLoop
       es_trace: empty
       es_cond_path: [0]

 ]

Successful States:
[
 Label: 
 State:HP_910(left_19_908) * HP_911(right_19_909) * x::node<val_19_907,left_19_908,right_19_909>@M[Orig]&right_19_909=ttt_30' & ttt_30'=null&{FLOW,(22,23)=__norm}[]
       es_var_measures 2: MayLoop
       es_trace: empty
       es_cond_path: [0]

 ]

*/

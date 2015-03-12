data node {
  node next;
}

HeapPred H(node a).
PostPred G(node a).

void foo(node x)
/*
 requires x::node<null>
 ensures x::node<null>;
*/
 infer [H,G]
 requires H(x)
 ensures G(x);
{
  node t;
  t = x.next;
  assert t'=null assume true;
  dprint;
}
/*

[ H(x) --> x::node<next_18_778>@M * H_9(next_18_778),
 H_9(next_18_778) * x::node<next_18_778>@M --> G(x)]
*

 id: 3; caller: []; line: 19; classic: false; kind: ASSERT/ASSUME; hec_num: 2; evars: []; infer_vars: [H,G,H_9]; c_heap: emp
 checkentail H_9(next_18_778) * x::node<next_18_778>@M[Orig]&x=x' & next_18_778=t_30'&
{FLOW,(22,23)=__norm}[]
 |-  emp&t_30'=null&{FLOW,(22,23)=__norm}[]. 
res:  [
  H_9(next_18_778) * x::node<next_18_778>@M[Orig]&x=x' & next_18_778=t_30'&{FLOW,(22,23)=__norm}[]
  ]

*/
  

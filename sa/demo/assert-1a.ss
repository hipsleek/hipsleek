data node {
  node next;
}

HeapPred H(node a).
PostPred G(node a).

void assertfoo(node x)
 requires x=null
 ensures true;

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
  assertfoo(t);
  //dprint;
}
/*
# assert-1a.ss


GOT
===
[ H(x) --> x::node<next_22_779>@M * HP_780(next_22_779),
 HP_780(next_22_779) * x::node<next_22_779>@M --> G(x)]

BUT
===
 H(x_786) ::=  x_786::node<next_22_779>@M&next_22_779=null,
 G(x_787) ::=  x_787::node<next_22_779>@M&next_22_779=null]

seems that HP_780(n) --> n=null
is captured but not printed; can we have --pred-dis-eup to show it

=====
[ H(x_786) ::=  x_786::node<next_22_779>@M&next_22_779=null,
 G(x_787) ::=  x_787::node<next_22_779>@M&next_22_779=null]

 id: 3; caller: []; line: 19; classic: false; kind: ASSERT/ASSUME; hec_num: 2; evars: []; infer_vars: [H,G,H_9]; c_heap: emp
 checkentail H_9(next_18_778) * x::node<next_18_778>@M[Orig]&x=x' & next_18_778=t_30'&
{FLOW,(22,23)=__norm}[]
 |-  emp&t_30'=null&{FLOW,(22,23)=__norm}[]. 
res:  [
  H_9(next_18_778) * x::node<next_18_778>@M[Orig]&x=x' & next_18_778=t_30'&{FLOW,(22,23)=__norm}[]
  ]

*/
  

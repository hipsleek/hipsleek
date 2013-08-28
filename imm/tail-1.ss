data node{
	int val;
	node next;
}

HeapPred H1(node a).
HeapPred G1(node a, node b).

node foo (node c)
  infer [ann1]
  requires c::node<a,b>@ann1
  ensures c::node<a,b> & res=b;

/*
  infer[H1,G1] 
  requires H1(c) 
  ensures G1(res,c);
*/
{
    return c.next;
}

/*
# tail-1.ss

Inferred pre is incorrect.

!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ ann1<=2]

However, --en-sleek-logging-txt gave the correct result:

  es_infer_pure: [ann1<=0; ann1<=2]

Thus hip is not working correctly for this example!

 id: 5; caller: []; line: 12; classic: false; kind: POST; hec_num: 4; evars: []; c_heap: c::node<a,b>@ann1[Orig]
 checkentail emp&ann1<=2 & b=v_node_20_776' & res=v_node_20_776' & a=a_32 & b=b_33 & 
ann1<=0&{FLOW,(22,23)=__norm}[]
 |-  emp&b=res & a=a_32 & b=b_33&{FLOW,(22,23)=__norm}[]. 
res:  [
  emp&ann1<=2 & b=v_node_20_776' & res=v_node_20_776' & a=a_32 & b=b_33 & ann1<=0&{FLOW,(22,23)=__norm}[]
  es_infer_vars/rel: [ann1]
  es_infer_pure: [ann1<=0; ann1<=2]
  ]
*/
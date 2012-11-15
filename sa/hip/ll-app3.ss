data node {
	int val; 
	node next;	
}

HeapPred H1(node a).
HeapPred H2(node a).
HeapPred H3(node a).
HeapPred G1(node a, node b).
HeapPred G2(node a, node b).

ls<> == self=null 
  or self::node<_,q>*q::ls<>
 inv true;


/*
  H3(r_589) * x'::node<val_23_561,r_589>&
    v_node_23_576!=null --> H3(x')&true
  H2(y) * HP_553(v_node_23_570) * 
    x'::node<val_23_559,y>&v_node_23_570=null --> H3(x') * HP_587(y)&true,
  H2(y)&true --> H2(y)&true
  HP_553(v_node_23_576)& v_node_23_576!=null --> H1(v_node_23_576)&true,
  H1(x)&true --> x::node<val_23_533',next_23_534'> 
   * HP_553(next_23_534')&true]
*/

void append(ref node x, node y)
  // requires x::ls<> * y::ls<> & x!=null
  // ensures x'::ls<>;
  infer [H1,H2,H3]
  requires H1(x)*H2(y)
  ensures H3(x');
{
	if (x.next == null){
	      x.next = y;	
}
	else {
	      node r=x.next;
	      append(r, y);
              x.next=r;
}
}


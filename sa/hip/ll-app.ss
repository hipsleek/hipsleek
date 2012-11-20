data node {
	int val; 
	node next;	
}

HeapPred H1(node a).
HeapPred H2(node a).
HeapPred H3(node a).
HeapPred G1(node a, node b).
HeapPred G2(node a, node b).

/*
ls<> == self=null 
  or self::node<_,q>*q::ls<>
 inv true;
*/

void append(ref node x, node y)
/*
  requires x::ls<> * y::ls<> & x!=null
  ensures x'::ls<>;
*/
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

/*
[ 

  //post
  H3(r_583) * x'::node<val_27_555,r_583>&
    v_node_27_570!=null --> H3(x')&true,

  H2(y) * HP_547(v_node_27_564) * 
  x'::node<_,y>&v_node_27_564=null --> H3(x') * HP_581(y)&true,

 RELASS [H2] H2(y)&true --> H2(y)&true,

 RELASS [HP_547,H1,H2]
  HP_547(v_node_27_570)&
  v_node_27_570!=null --> H1(v_node_27_570)&true,

 RELASS [H1,H2,HP_547]
  H1(x)&true --> x::node<val_27_527',next_27_528'> * 
  HP_547(next_27_528')&true]


*/


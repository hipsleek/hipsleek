data node {
	int val;
	node next
}

HeapPred H1(node a).
HeapPred G4(node a, node b, node c).

/* return the tail of a singly linked list */
node get_next(ref node x)
  infer[H1,G4]
  requires H1(x)
  ensures G4(res,x',x);//'
/*

[ HP_RELDEFN HP_559
HP_559(v_node_31_548') ::=UNKNOWN,
 HP_RELDEFN G4
G4(v_node_31_548',x,v_571) ::= HP_559(v_node_31_548') * x::node<val_29_568,next_30_547'>&
next_30_547'=null & x=v_571,
 HP_RELDEFN H1
H1(x) ::= x::node<val_29_543',next_29_544'> * HP_559(next_29_544')&true]

*/
{
  node tmp = x.next;
  x.next = null;
  return tmp;
  //	dprint;
}



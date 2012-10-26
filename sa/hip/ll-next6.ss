data node {
	int val;
	node next
}

HeapPred H1(node a,node b).
HeapPred G4(node a, node b, node c, node d).

/* return the tail of a singly linked list */
node get_next(ref node x)
  infer[H1,G4]
  requires H1(x,q)
  ensures G4(res,x',x,p);//'

/*  requires x::node<_,_,null>
  ensures true;
*/
/*

[ HP_RELDEFN HP_550
HP_550(v_node_32_529',q2) ::=UNKNOWN,
 HP_RELDEFN G4
G4(next_31_528',x,v_548,q2) ::= HP_550(next_31_528',q2)&x=v_548,
 HP_RELDEFN H1
H1(x) ::= HP_550(next_31_528',q2) * HP_550(next_31_528',q2)&true]

ERROR : H1 should have 2 parameters..
*/
{
  node tmp = x.next;
  return tmp;
  //	dprint;
}



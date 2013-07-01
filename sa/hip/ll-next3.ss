data node {
	int val;
	node next
}


HeapPred G4(node a, node b, node c, node d).

/* return the tail of a singly linked list */
node get_next(ref node x)
  infer[G4]
  requires x::node<_,q>
  ensures G4(x',x,res,q);//'
             /*
  requires x::node<_,q> 
  ensures x::node<_,null> & res=q & x'=x; //'

[ HP_RELDEFN G4
G4(x,v_570,v_node_40_552',q) ::= x::node<Anon_12,next_39_551'>&x=v_570 & v_node_40_552'=q & next_39_551'=null]

*/
{
  node tmp = x.next;
  x.next = null;
  return tmp;
  //	dprint;
}



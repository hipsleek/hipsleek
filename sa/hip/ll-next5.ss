data node {
	int val;
	node next
}

HeapPred H1(node a).
HeapPred G4(node a, node b, node c, node d).

/* return the tail of a singly linked list */
node get_next(ref node x)
  infer[H1,G4]
  requires H1(x)
  ensures G4(res,x',x);//'
/*

[ HP_RELDEFN H1
H1(x) ::= 
 H1(x)&x=v_563 & x=v_563
 or x::node<val_36_543',next_36_544'> * x::node<val_36_562,next_36_544'>&true
 ,
 HP_RELDEFN G4
G4(next_36_544',x,v_563) ::= H1(x)&x=v_563]

ERROR : why is there a disjunction in H1?

*/
{
  node tmp = x.next;
  return tmp;
  //	dprint;
}



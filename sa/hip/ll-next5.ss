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

HP_545(next_31_525') ::=UNKNOWN,
 HP_RELDEFN G4
G4(next_31_525',x,v_544) ::= x::node<val_31_543,next_31_525'> * HP_545(next_31_525')&x=v_544,
 HP_RELDEFN H1
H1(x) ::= x::node<val_31_543,next_31_525'> * HP_545(next_31_525')&true]

ERROR : should be an error that number of parameters of G4 is
 wrong..
*/
{
  node tmp = x.next;
  return tmp;
  //	dprint;
}



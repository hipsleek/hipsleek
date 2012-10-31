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


             /*
!!!    new hrel:  RELASS [H1,HP_541] unknown svl: [next_30_528'];  unknown hps: [HP_549];  predefined: ;
 H1(x)& true --> x::node<val_30_527',next_30_528'> * HP_541(next_30_528',x) * HP_549(next_30_528')&true
!!!    new hrel:  RELASS [HP_541,G4] unknown svl: [v_node_31_529'; p];  unknown hps: [HP_549; 
  HP_550];  predefined: ; HP_541(v_node_31_529',x) * 
  x::node<val_30_547,v_node_31_529'> * HP_549(v_node_31_529')&
  true --> G4(v_node_31_529',x,v_548,p) * HP_550(v_node_31_529',p)&x=v_548

[
HP_541(v_node_31_529',x,q) *  x::node<val_30_547,v_node_31_529'>&true --> G4(v_node_31_529',x,v_549,p) * HP_548(q)&x=v_549,

H1(x,q)&true --> x::node<val_30_527',next_30_528'> * HP_541(next_30_528',x,q)&true]
              */

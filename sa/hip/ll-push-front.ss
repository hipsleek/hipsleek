/* singly linked lists */

/* representation of a node */
data node {
	int val;
	node next;
}

/* view for a singly linked list */
ll<n> == self = null & n = 0
	or self::node<_, q> * q::ll<n-1>
  inv n >= 0;

HeapPred H(node a).
HeapPred H1(node a).
HeapPred H2(node a).
HeapPred G(node a, node b).
HeapPred G1(node a, node b).
HeapPred G2(node a, node b).
HeapPred G3(node a, node b, node c).
HeapPred G4(node a, node b, node c, node d).


void dispose(ref node x)
  requires x::node<_,_>
  ensures x'=null;

void push_front(ref node x, int v)
  infer[H, G]
  requires H(x)
  ensures G(x,x'); //'m=n+1
{
  node tmp = new node(v,x);
  x = tmp;
}

/*
H(x) * x'::node<v,x> --> G(x,x')
!!! NEW HP ASSUME:[ (H(x) * x'::node<v,x>&true) --> G(x,x')&true]
!!! NEW SIMPLIFIED HP ASSUME:[HP_RELDEFN H:  H(x)::  HP_995(x)&true,
HP_RELDEFN G:  G(x,x')::  HP_995(x) * HP_996(x')&true]

//SHOULD NOT SPLIT

*/

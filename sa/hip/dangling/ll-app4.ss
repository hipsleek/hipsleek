data node {
	int val; 
	node next;	
}

HeapPred H1(node a).
HeapPred H2(node a).
HeapPred H3(node a).
HeapPred H4(node a).
HeapPred G1(node a, node b).
HeapPred G2(node a, node b).

ls<> == self=null 
  or self::node<_,q>*q::ls<>
 inv true;

void append(ref node x, node y)
/*
  requires x::ls<> * y::ls<> & x!=null
  ensures x'::ls<>;
*/
/*

We got:

[ H3(x_581) ::= x_581::node<val_54_544,y>@M * HP_582(y)&true,
 H1(x_587) ::= x_587::node<val_54_522',next_54_523'>@M * next_54_523'::ls[LHSCase]&true,
 H2(y) ::= H4(y)&true,
 HP_582(y) ::= 
 y::node<val_54_544,y_585>@M * HP_582(y_585)&true
 or emp& XPURE(H2(y))
 ]

However, H2(y) is an input predicate (in precondition), while
H4(y) is an output predicate. Hence, we should have the
following instead:

 H4(y) ::= H2(y)&true,

Once you have this, then --sa-dangling should simply introduce:

 H2(y) ::= emp & DLING_H2 = y

With this --sa-inlining would produce the desired result

*/
  infer [H1,H2,H3,H4]
  requires H1(x)*H2(y)
  ensures H3(x')*H4(y);//'

{
    node t = x.next;
	if (t == null){
	      x.next = y;	
}
	else {
	      append(t, y);
              x.next=t;
}
}



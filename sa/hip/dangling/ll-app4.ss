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

*************************************
*******relational definition ********
*************************************
[ H4(y_580) ::= H2(y_580)&true,
 H3(x_581) ::= x_581::node<val_52_544,y>@M * HP_582(y)&true,
 H1(x_587) ::= x_587::node<val_52_522',next_52_523'>@M * next_52_523'::ls[LHSCase]&true,
 HP_582(y) ::= 
 y::node<val_52_544,y_585>@M * HP_582(y_585)&true
 or emp& XPURE(H2(y))
 ]

Once you have this, then --sa-dangling should simply introduce:

 H4(y_580) ::= emp&DLING_H2_y_593=y_580,
 H2(y) ::= emp&DLING_H2_y_593=y,

I think we should have instead:
 H4(y_580) ::= H2(y_580)&true,
 H2(y) ::= emp & DLING_H2 = y

After that --sa-inlining would replace all occurrences of
H2(..).


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



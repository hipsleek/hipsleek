data node {
	int val; 
	node next;	
}

HeapPred H1(node a).
HeapPred H2(node a).
HeapPred H3(node a).
HeapPred G1(node a, node b).
HeapPred G2(node a, node b).

ls<> == self=null 
  or self::node<_,q>*q::ls<>
 inv true;


/*

[ H3(x_587) ::= x_587::node<val_52_546,y>@M * HP_588(y)&true,
 H1(x_594) ::= x_594::node<val_52_521',next_52_522'>@M * next_52_522'::ls[LHSCase]&true,
 H2(y) ::= emp&DLING_H2_y_600=y,
 HP_588(y) ::= 
 emp&DLING_H2_y_600=y
 or y::node<val_52_546,y_591>@M * HP_588(y_591)&true
 ]

*/

void append(ref node x, node y)
  // requires x::ls<> * y::ls<> & x!=null
  // ensures x'::ls<>;
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


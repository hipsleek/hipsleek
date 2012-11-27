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
[ H1(x)&true --> x::node<val_31_522',next_31_523'> * HP_539(next_31_523')&true,
 HP_539(t_21')&t_21'!=null --> H1(t_21')&true,
 H2(y)&true --> H2(y)&true,
 HP_539(next_33_551)&next_33_551=null --> emp&true,
 x'::node<val_31_544,y>&H2_y_563=y --> H3(x')&true,
 H2(y)&H2_y_563=y --> H4(y)&true,
 H3(t_565) * x'::node<val_31_546,t_565>&true --> H3(x')&true,
 H4(y)&true --> H4(y)&true]

..


[ H3(x_581) ::= x_581::node<val_31_544,y> * HP_582(y)&true,
 H1(x_587) ::= x_587::node<val_31_522',next_31_523'> * next_31_523'::ls[LHSCase]&true,
 H2(y) ::= emp&H2_y_563=y,
 H4(y) ::= emp&H2_y_563=y,
 HP_582(y) ::= 
 emp&H2_y_563=y
 or y::node<val_31_544,y_585> * HP_582(y_585)&true
 ]


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



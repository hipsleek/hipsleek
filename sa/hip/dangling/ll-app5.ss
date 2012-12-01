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

  G1(x,y)&true --> x::node<val_27_522',next_27_523'>@M * HP_539(next_27_523',y)&true,
  HP_539(t_21',y)&t_21'!=null --> G1(t_21',y)&true,
  HP_539(next_29_551,y) * x'::node<val_27_544,y>@M&
       next_29_551=null --> G2(x',y)&true,
  G2(t_564,y) * x'::node<val_27_546,t_564>@M&true --> G2(x',y)&true]

G2(x_574,y_575) ::= x_574::node<val_27_544,y_575_576>@M * HP_577(y_575_576,y_575) * HP_565(y_575)&true,
G1(x_582,y_583) ::= x_582::node<val_27_522',next_27_523'>@M * HP_584(next_27_523',y_583) * HP_565(y_583)&true,
HP_577(y_575_576,y_575) ::= 
 y_575_576::node<val_27_544,y_575_580>@M * HP_577(y_575_580,y_575)&true
 or emp&y_575=y_575_576
 ,
HP_584(next_27_523',y_583) ::= 
 next_27_523'::node<val_27_522',next_27_587>@M * HP_584(next_27_587,y_583)&
 true 


G2(x,y_583) ::= x::node<val_48_544,y_583_584>@M * HP_585(y_583_584,y_583) * HP_566(y_583)&true,
G1(x,y) ::= HP_568(y) * x::node<val_48_522',next_48_523'>@M * next_48_523'::ls[LHSCase]& true,
HP_566(y) ::= HP_568(y)&true,
HP_585(y_583_584,y_583) ::= 
 y_583_584::node<val_48_544,y_583_588>@M * HP_585(y_583_588,y_583)&true
 or emp&y_583=y_583_584



*/


  infer [G1,G2]
  requires G1(x,y)
  ensures G2(x',y);//'

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



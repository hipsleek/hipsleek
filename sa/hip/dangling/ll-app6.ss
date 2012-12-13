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

 H1(x)&true --> x::node<val_56_522',next_56_523'>@M * HP_539(next_56_523')& true,
 HP_539(t_21')&t_21'!=null --> H1(t_21')&true,
 H2(y)&true --> H2(y)&true,
 HP_539(next_58_551)&next_58_551=null --> emp&true,

 H2(y) * x'::node<val_56_544,y>@M&true --> G2(x',y)&true,
 G2(t_564,y) * x'::node<val_56_546,t_564>@M&true --> G2(x',y)&true]

*************************************

 H1(x_587) ::= x_587::node<val_56_522',next_56_523'>@M * next_56_523'::ls[LHSCase]&true,

 G2(x_578,y_579) ::= x_578::node<val_56_544,y_579_580>@M * HP_581(y_579_580,y_579) * H2(y_579)&true,
 HP_581(y_579_580,y_579) ::= 
   y_579_580::node<val_56_544,y_579_584>@M * HP_581(y_579_584,y_579)&true
   or emp&y_579=y_579_580
 
**************************************
For ll-app6.ss, we obtained rel-ass:

 H2(y) * x'::node<val_56_544,y>@M&true --> G2(x',y)&true,
 G2(t_564,y) * x'::node<val_56_546,t_564>@M&true --> G2(x',y)&true]

I am a little surprised that norm obtained:

 G2(x_578,y_579) ::= x_578::node<val_56_544,y_579_580>@M * HP_581(y_579_580,y_579) * H2(y_579)&true,
 HP_581(y_579_580,y_579) ::= 
   y_579_580::node<val_56_544,y_579_584>@M * HP_581(y_579_584,y_579)&true
   or emp&y_579=y_579_580

I think, it should be easy to obtain simply:

 G2(x_578,y_579) ::= x_578::node<val_56_544,y_579_580>@M * HP_581(y_579_580,y_579) 
 HP_581(y_579_580,y_579) ::= 
   y_579_580::node<val_56_544,y_579_584>@M * HP_581(y_579_584,y_579)&true
   or emp&H2(y_529)

Also, you should not be generating y_579_580 but should instead generate y_580.
There is a way to do that in our generator.



*/


  infer [H1,H2,G2]
  requires H1(x) * H2(y)
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



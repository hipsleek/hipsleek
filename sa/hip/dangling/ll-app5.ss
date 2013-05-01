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
HeapPred G3(node a, node b,node c).

ll<> == self=null
  or self::node<_,q>*q::ll<>
 inv true;

lseg<p> == self=p 
  or self::node<_,q>*q::lseg<p>
 inv true;

void append(ref node x, node y)
/*
  requires x::ls<> * y::ls<> & x!=null
  ensures x'::ls<>;

*************************************
*******relational assumption ********
*************************************
[ G1(x,y)&true --> x::node<val_65_528',next_65_529'>@M * 
  HP_545(next_65_529',y)&true,
 HP_545(t_22',y)&t_22'!=null --> G1(t_22',y)&true,
 HP_545(next_67_557,y) * x'::node<val_65_550,y>@M&x=x' & 
  next_67_557=null --> G3(x',x,y)&true,
 G3(t_570,t_567,y) * x'::node<val_65_552,t_570>@M&t_567!=null & 
  x=x' --> G3(x',x,y)&true]

*************************************
*******relational definition ********
*************************************
*************************************
[ G3(x_580,x_581,y_582) ::= x_580::node<val_65_550,y_582_583>@M * HP_584(y_582_583,x_581,y_582) * 
HP_571(y_582)&x_580=x_581,
 G1(x_592,y_593) ::= x_592::node<val_65_528',next_65_529'>@M * HP_594(next_65_529',y_593) * 
HP_571(y_593)&true,
 HP_584(y_582_583,x_591,y_582) ::= 
 y_582_583::node<val_65_550,y_582_589>@M * HP_584(y_582_589,t_567,y_582)&true
 or emp&y_582=y_582_583
 ,
 HP_594(next_65_529',y_593) ::= 
 next_65_529'::node<val_65_528',next_65_597>@M * HP_594(next_65_597,y_593)&
 true
 or emp&next_65_529'=null


Elimination of Parameters
=========================
Given an intermediate predicate, determine a set of parameters 
that are required for the definition. Provide this step
prior to equivalence checking.

// can we eliminate the 2nd parameter below?
 HP_600(next_65_535',y_599) ::= 
 next_65_535'::node<val_65_534',next_65_603>@M * HP_600(next_65_603,y_599)&
 true
 or emp&next_65_535'=null


// can we eliminate the 2nd parameter below?
 HP_590(y_588_589,x_597,y_588) ::= 
 y_588_589::node<val_65_556,y_588_595>@M * HP_590(y_588_595,t_573,y_588)&true
 or emp&y_588=y_588_589,

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



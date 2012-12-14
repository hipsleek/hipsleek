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
[ G1(x,y)&true --> x::node<val_82_534',next_82_535'>@M * 
  HP_551(next_82_535',y)&true,
 HP_551(t_24',y)&t_24'!=null --> G1(t_24',y)&true,
 HP_551(next_84_563,y) * x'::node<val_82_556,y>@M&x=x' & 
  next_84_563=null --> G3(x',x,y)&true,
 G3(t_576,t_573,y) * x'::node<val_82_558,t_576>@M&t_573!=null & 
  x=x' --> G3(x',x,y)&true]
*************************************

*************************************
*******relational definition ********
*************************************
G3(x_586,x_587,y_588) ::= x_586::node<val_82_556,y_588_589>@M * y_588_589::lseg<y_588>[LHSCase] * HP_577(y_588)&x_586=x_587,
 G1(x_597,y_598) ::= x_597::node<val_82_534',next_82_535'>@M * next_82_535'::ll[LHSCase] * 
HP_577(y_598)&true]


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


  infer [G1,G3]
  requires G1(x,y)
  ensures G3(x',x,y);//'

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



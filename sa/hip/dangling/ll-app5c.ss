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

Expecting:
 G1(x,y) ::= x::node<_,n>*n::ll<> 
 G3(x',x,y) ::= x::node<_,n> * n::ls<y> & x'=x

but Obtained:
*************************************
*******relational definition ********
*************************************
G3(x_586,x_587,y_588) ::= x_586::node<val_82_556,y_588_589>@M * y_588_589::lseg<y_588>[LHSCase] * HP_577(y_588)&x_586=x_587,
 G1(x_597,y_598) ::= x_597::node<val_82_534',next_82_535'>@M * next_82_535'::ll[LHSCase] * 
HP_577(y_598)&true]

PROBLEM : Why is there a HP_577(..)?
  Did this come from elim useless parameter?
  Can you provide option --sa-dis-useless?
  and also print before and after this elim technique,
  as I would like to see if HP_577 was introduced by
  useless param elim?


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



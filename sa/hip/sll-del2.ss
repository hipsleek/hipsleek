data node2 {
	int val;
	node2 next;
}

sll<> == self = null 
  or self::node2<_ ,q> * q::sll<> // = q1
	inv true;
HeapPred G1(node2 a).
HeapPred H1(node2 a).
HeapPred G2(node2 a).

node2 delete(node2 x)
  /* infer[n] */
/*
  requires x::node2<_,q>*q::sll<> & q!=null 
  ensures x::node2<_,r>*r::sll<> ;
  requires x::node2<_,q>*q::node2<_,q1> * q1::sll<> 
  ensures x::node2<_,r>*r::sll<> ; 
  requires x::node2<_,q>*q::node2<_,q1> * q1::sll<> 
  ensures x::node2<_,r>*r::sll<>*res::node2<_,null>; 

*/
  infer[H1,G1,G2]
  requires H1(x)
  ensures G1(x) * G2(res);

{
  bool l = x.next.next==null;
  if (l) {
    node2 y;
    y = x.next;
    x.next = null;
    return y;
    }
  else
    return delete(x.next);
}


/*

We obtained :

 G2(res) ::= res::node2<val_30_567,v_node2_30_579>@M&true]

but why did we not get:

 G2(res) ::= res::node2<val_30_567,null>@M&true]

This problem seems to be triggered at relational assumption:

 res::node2<val_30_567,v_node2_30_579>@M&true --> G2(res)&true,


[ H1(x_607) ::= x_607::node2<val_30_528',next_30_529'>@M * 
next_30_529'::node2<val_30_531',next_30_605>@M * next_30_605::sll@M[LHSCase]&
true,
 G1(x_614) ::= x_614::node2<val_30_560,next_34_538'>@M * next_34_538'::sll@M[LHSCase]&true,
 G2(res) ::= res::node2<val_30_567,v_node2_30_579>@M&true]

*/

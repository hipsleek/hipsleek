data node2 {
	int val;
	node2 prev;
	node2 next;
}

dll<p> == self = null 
  or self::node2<_ ,p , q> * q::dll<self> // = q1
	inv true;

HeapPred G1(node2 a).
HeapPred H1(node2 a).

void insert(node2 x, int a)
  /* infer[n] */
/*
  requires x::dll<p> & x!=null
  ensures x::dll<p> ;
*/

  infer[H1,G1]
  requires H1(x)
  ensures G1(x);

{
  bool l = x.next == null;
  if (l)
    x.next = new node2(a, x, null);
  else
    insert(x.next, a);
}

/*

H1(x) ::= x::node<_,p,q> * HP(q) * HD(p)
HP(x) ::= x=null
      or x::node<_,p,q>*HP(q) * HD2<p>

G1(x) ::= x::node<_,p,q> * HP2(q) * HD(p)

HP2(x) ::= x::node<_,p,null> * ?(p)
      or x::node<_,p,q> * HP2(q) * HD2(p)

HP2(x) ::= x::node<_,p,null> * ?(p)
      or x::node<_,p,q> * HP2(q) * HD2(p)

 G1(x_603) ::= x_603::node2<val_26_564,prev_26_565,v_node2_28_596>@M * 
HP_604(prev_26_565,v_node2_28_596) * HP_557(prev_26_565)&true,

 H1(x_610) ::= 
 HP_604(prev_26_565,v_node2_28_596) * HP_557(prev_26_565)&true
 or x_610::node2<val_26_534',prev_26_535',next_26_536'>@M * 
    HP_557(prev_26_535') * HP_558(next_26_536')&true
 ,
 HP_558(v_node2_26_602) ::= 
 emp&v_node2_26_602=null
 or v_node2_26_602::node2<val_26_534',prev_26_535',next_26_536'>@M * 
    HP_557(prev_26_535') * HP_558(next_26_536')&true
 ,
 HP_604(prev_26_565,v_node2_28_596) ::= 
 emp&v_node2_28_596=null
 or v_node2_28_596::node2<val_26_564,prev_26_605,v_node2_28_606>@M * 
    HP_604(prev_26_605,v_node2_28_606)&true
 ]


 
 */

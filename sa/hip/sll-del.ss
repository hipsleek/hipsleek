data node2 {
	int val;
	node2 next;
}

/*
sll<> == self = null 
  or self::node2<_ ,q> * q::sll<> // = q1
	inv true;
*/
HeapPred G1(node2 a).
HeapPred H1(node2 a).

void delete(node2 x)
  /* infer[n] */
/*
  requires x::node2<_,q>*q::sll<> & q!=null
  ensures x::node2<_,r>*r::sll<> ;
  requires x::node2<_,q>*q::node2<_,q1> * q1::sll<> 
  ensures x::node2<_,r>*r::sll<> ; 
*/
  infer[H1,G1]
  requires H1(x)
  ensures G1(x);
{
  bool l = x.next.next==null;
  if (l) {
    x.next = null;
    }
  else
    delete(x.next);
}


/*

[ G1(x_589) ::= x_589::node2<val_27_548,next_29_528'>@M 
              * HP_590(next_29_528')&true,

 H1(x_594) ::= x_594::node2<val_27_520',next_27_521'>@M * 
    next_27_521'::node2<val_27_523',next_27_587>@M&next_27_587=null,

 HP_590(next_29_528') ::= 
 emp&next_29_528'=null
 or next_29_528'::node2<val_27_548,next_29_591>@M * HP_590(next_29_591)&true
 ]




*/

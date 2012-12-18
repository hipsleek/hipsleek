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

int count(node2 x)
  /* infer[n] */
/*
  requires x::dll<p> 
  ensures x::dll<p> ;
*/

  infer[H1,G1]
  requires H1(x)
  ensures G1(x);

{
  if (x==null)
    return 0;
  else
    return 1+count(x.next);
}

/*

[ H1(x_579) ::= 
 emp&x_579=null
 or x_579::node2<val_29_577,prev_29_578,next_29_535'>@M * 
    HP_557(prev_29_578) * H1(next_29_535')&true
 ,
 G1(x_580) ::= H1(x_580)&true]

*/

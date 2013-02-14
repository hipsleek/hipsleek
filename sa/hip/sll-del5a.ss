data node {
	int val;
	node next;
}

sll<> == self = null 
  or self::node<_ , q> * q::sll<> // = q1
	inv true;

HeapPred G1(node a).
HeapPred H1(node a).

void delete(node x)
  /* infer[n] */

/*

  requires x::node<_,q>*q::sll<> & q!=null
  ensures x::node<_,r>*r::sll<> ;

  requires x::node<_,q>*q::sll<> & q!=null
  ensures x::node<_,r>*r::sll<> ;

*/


  /* requires dll<p> */
  /* ensures  dll<q>; */
/*

  requires x::node<_,q>*q::sll<> 
  ensures x::node<_,r>*r::sll<> ;

*/


  infer[H1]
  requires H1(x)
  ensures  H1(x);

{
  bool l = x.next.next==null;
  if (l) {
    // dprint;
    x.next = null;
    }
  else
    delete(x.next);
}


/*

  infer[H1,G1]
  requires H1(x)
  ensures  G1(x);

[ H1(x_599) ::= x_599::node<val_33_526',next_33_527'>@M * 
   next_33_527'::node<val_33_529',next_33_597>@M 
   * next_33_597::sll@M[LHSCase]&
true,
 G1(x_606) ::= x_606::node<val_33_554,next_36_534'>@M 
   * next_36_534'::sll@M[LHSCase]&true]

  infer[H1]
  requires H1(x)
  ensures  H1(x);

===========================================================

[ H1(x_613) ::= x_613::node<val_33_554,next_36_534'>@M * 
                     next_36_534'::sll@M[LHSCase]&true]


*/

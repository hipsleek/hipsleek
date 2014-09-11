data node { int val; node next; }

/* piecewise/conditional amortized ranking function */

ll<r> == 
  self = null & r = 0 or
  self::node<v, p> * p::ll<r1> 
		& (v = 0 & r = 1 + r1 | v != 0 & r = 2 + r1)
	inv r >= 0;

void dummy (node x)
  requires x::ll<r> & Term[r]
  ensures true;
{
  if (x == null) return;
  else if (x.val == 0) {
    dummy(x.next);
	} else {
    x.val = 0;
		return dummy(x);
  }
}

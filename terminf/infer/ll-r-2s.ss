data node {
  int val;
  node next;
}


ll<r> == 
  self = null & r = 0 or
  self::node<v, null> & r = 1 or 
  self::node<v1, p> * p::node<v2, null> & r = 1 or
  self::node<v, q> * q::ll<r1> & r = 1 + r1
	inv r >= 0;

/*
ll<r> == 
  self = null & r = r0 or 
  self::node<v, q> * q::ll<r1> & r = f(v, r1);
*/

int length (node x)
  requires x::ll<r> & Term[r]
  ensures res >= 0;
{
  if (x == null) {
		//dprint;
    return 0;
	} else {
		//dprint;
    int l = 1 + length(x.next);
		//dprint;
		return l;
	}
}



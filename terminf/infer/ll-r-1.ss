data node {
  int val;
  node next;
}


ll<> == 
  self::node<v, null> or 
  self::node<v, q> * q::ll<>;

/*
ll<r> == 
  self = null & r = r0 or 
  self::node<v, q> * q::ll<r1> & r = f(v, r1);
*/

int length (node x)
  requires x::ll<>
  /* requires x::ll<r> & Term[r] */
  ensures true;
{
  if (x.next == null) {
		//dprint;
    return 1;
	} else {
		//dprint;
    int l = 1 + length(x.next);
		//dprint;
		return l;
	}
}

/*
Generated Constraints:
  r0 >= 0
  r1 >= 0 => r = f(v, r1) = a*v + b*r1 + c >= 0 (redundant)
  
  r = f(v, r1) = a*v + b*r1 + c > r1
  (forall v, r1>=0) a*v + (b-1)*r1 + c > 0
  
  => a = 0; b = 1; c = 1
     r0 = 0
*/

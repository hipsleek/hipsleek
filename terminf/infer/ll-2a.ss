data node {
  int val;
  node next;
}


ll<s> == 
  self = null & s = 0 or 
  self::node<v, q> * q::ll<s1> & s = s1 + v & v>=0;

int length (node x)
  requires x::ll<s> 
  ensures res >= 0;
{
  if (x == null) {
		//dprint;
    return 0;
	} else {
    return 1 + length(x.next);
	}
}


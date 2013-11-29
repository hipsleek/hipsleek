data node {
  int val;
  node left;
	node right;
}


tree<s> == 
  self = null & s = 0 or 
  self::node<v, l, r> * l::tree<s1> * r::tree<s2> & s = 1 + s1 + s2
	inv s>=0;

int size (node x)
  requires x::tree<s>
  ensures res >= 0;
{
  if (x == null) {
    return 0;
	} else {
    int l = size(x.left);
		int r = size(x.right);
		return 1 + l + r;
	}
}



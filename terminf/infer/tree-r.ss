data node {
  int val;
  node left;
	node right;
}


tree<> == 
  self = null or 
  self::node<v, l, r> * l::tree<> * r::tree<>;

int size (node x)
  requires x::tree<>
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



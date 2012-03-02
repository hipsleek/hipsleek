data node {
	node left;
	node right; 
}

BTreeR<n, h> == 
	self = null & n = 0 & h = 0
	or self::node<p, q> * p::BTreeR<n1, h1> * q::BTreeR<n2, h2> & n = 1 + n1 + n2 & h = 1 + max(h1, h2)
	inv n >= 0 & h >= 0;

node create (int height)
case {
	height>=00 -> requires Term[height] ensures res::BTreeR<n, height> & n>=height;
	height<0 -> requires Loop ensures false;
}
{
	if (height == 0) 
		return null;
	else {
		node left = create (height - 1);
		node right = create (height - 1);
		return new node(left, right);
	}
}

int height (node x)
requires x::BTreeR<n, h>@L
ensures res=h;
{
	if (x == null)
		return 0;
	else {
		node l = x.left;
		node r = x.right;
		if (l == null && r == null)
			return 1;
		else if (l == null)
			return 1 + height(r);
		else 
			return 1 + height(l);
	}
}

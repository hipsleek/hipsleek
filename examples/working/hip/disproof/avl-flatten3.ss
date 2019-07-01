data node {
	int val;
	int height;
	node left;
	node right;
}

/* view for avl trees */
avl<size, height> == self = null & size = 0 & height = 0 
	or self::node<_, height, p, q> * p::avl<size1, height1> * q::avl<size2,
  height2> & size = 1+size1+size2 & height2<=height1+1 &
  height1<=height2+1 & height = max(height1, height2) + 1  
	inv size >= 0 & height >= 0;

dll<p, n> == self = null & n = 0 
	or self::node<_,_, p, q> * q::dll<self, n1> & n = n1+1
	inv n >= 0;

node append(node x, node y)
	requires x::dll<_, m> * y::dll<_, n>
	ensures res::dll<r, m+n>;
{
	node z;

	if (x == null)
		return y;
	else
	{
		z = append(x.right, y);
		x.right = z;
		if (z != null)
			z.left = x;
		return x;
	}
}


void flatten(node x)
	requires x::avl<s, h> 
	ensures (exists q : x::dll<q, s> & q=null);
{
	node tmp;
	if (x != null)
	{
		flatten(x.left);
		flatten(x.right);
		tmp = append(x.left, x.right);
		x.left = null;
		x.right = tmp.left;
		if (tmp != null)
			tmp.left = x;
	}
}


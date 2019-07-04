data node2 {
	node2 left;
	node2 right; 
}

tree<m, n> == self = null & m = 0 & n = 0 
	or self::node2<p, q> * p::tree<m1, n1> * q::tree<m2, n2> & m = 1 + m1 + m2 & n = 1 + max(n1, n2)
	inv m >= 0 & n >= 0;

dll<p, n> == self = null & n = 0 
	or self::node2<p, q> * q::dll<self, n1> & n = n1+1
	inv n >= 0;

node2 append(node2 x, node2 y)
	requires x::dll<_, m> * y::dll<_, n>
	ensures res::dll<r, m+n>;
{

	if (x == null)
		return y;
	else {
   	node2 z;
		z = append(x.right, y);
		x.right = z;
		if (z != null)
			z.left = x;

		return x;
	}
}


void flatten(node2 x)
	requires x::tree<m, n> 
	ensures (exists q : x::dll<q, m> & q=null);
{
	if (x != null)
	{
    flatten(x.left);
		flatten(x.right);
		node2 tmp;
		tmp = append(x.left, x.right);
		x.left = null;
		x.right = tmp;
		if (tmp != null)
    //   tmp.left = x;
    tmp.right = x;
	}
}


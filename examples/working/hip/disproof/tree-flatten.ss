/* trees & binary search trees */

/* representation of a node */
data node {
	int val; 
	node next;	
}

data node2 {
	int val;
	node2 left;
	node2 right; 
}

/* view for trees with number of nodes and depth */
tree<m, n> == self = null & m = 0 & n = 0 
	or self::node2<_, p, q> * p::tree<m1, n1> * q::tree<m2, n2> & m = 1 + m1 + m2 & n = 1 + max(n1, n2)
	inv m >= 0 & n >= 0;

/*tree_1<S> == self = null & S = {}
	or self::node2<v, p, q> * p::tree_1<S1> * q::tree_1<S2> & S = union(S1, S2, {v});*/

/* view for a doubly linked list with size */
dll<p, n> == self = null & n = 0 
	or self::node2<_, p, q> * q::dll<self, n1> & n = n1+1
	inv n >= 0;


node2 append(node2 x, node2 y)

	requires x::dll<_, m> * y::dll<_, n>
	ensures res::dll<r, m+n>;

{
	node2 z;

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


/*node2 append1(node2 x, node2 y)

	requires x::dll1<_, S1> * y::dll1<_, S2>
	ensures res::dll1<r, S3> & S3 = union(S1, S2);

{
	node2 z;

	if (x == null)
		return y;
	else
	{
		z = append1(x.right, y);
		x.right = z;
		if (z != null)
			z.left = x;

		return x;
	}
}*/


/* function to transform a tree in a doubly linked list */
void flatten(node2 x)
	requires x::tree<m, n> 
	ensures (exists q : x::dll<q, m> & q=null);
{
	node2 tmp;
	if (x != null)
	{
		flatten(x.left);
		flatten(x.right);
		tmp = append(x.left, x.right);
		x.left = null;
		x.right = tmp;
		if (tmp != null)
			tmp.left = x;
	}
}

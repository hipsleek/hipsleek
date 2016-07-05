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

/* view for a doubly linked list with size */
dll<p, n> == self = null & n = 0 
	or self::node2<_, p, q> * q::dll<self, n1> & n = n1+1
	inv n >= 0;

/* function to append 2 doubly linked lists */
node2 append(node2 x, node2 y)

	requires x::dll<_, m> * y::dll<_, n> & Term[m]
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

/* function to count the number of nodes in a tree */
int count(node2 z)

	requires z::tree<m, n> & Term[m]
	ensures z::tree<m, n> & res = m & res >= 0;

{
	int cleft, cright;

	if (z == null)
		return 0;
	else
	{
		cleft = count(z.left);
		cright = count(z.right);
		return (1 + cleft + cright);
	}
}

/* function to transform a tree in a doubly linked list */
void flatten(node2 x)
	requires x::tree<m, n> & Term[m] 
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

/* binary search trees */

/* view for binary search trees */
bst <n, sm, lg> == self = null & n = 0 & sm <= lg 
	or (exists pl,qs: self::node2<v, p, q> * p::bst<n1, sm, pl> * q::bst<n2, qs, lg> & pl <= v & qs >= v & n=1+n1+n2)
	inv n>= 0 & sm <= lg;

/* insert a node in a bst */
node2 insert(node2 x, int a)

	requires x::bst<n, sm, lg> & Term[n] 
	ensures res::bst<n+1, mi, ma> & res != null & mi = min(sm, a) & ma = max(lg, a);
	
{
	node2 tmp;
        node2 tmp_null = null;

	if (x == null)
		return new node2(a, null, null);
	else
	{
		if (a <= x.val)
		{
			tmp = x.left;
			x.left = insert(tmp, a);
		}
		else
		{ 
			//tmp = x.right;
			x.right = insert(x.right, a);
		}

		return x;
	} 
}

/* delete a node from a bst */

int remove_min(ref node2 x)

	requires x::bst<n, s, b> & x != null & Term[n] 
	ensures x'::bst<n1, s1, b> & s <= res <= s1 & n1<n;

{
	int tmp, a; 

	if (x.left == null)
	{
		tmp = x.val;
		x = x.right;

		return tmp; 
	}
	else {
		int tmp;
		bind x to (_, xleft, _) in { 
			tmp = remove_min(xleft);
		}

		return tmp;
	}
}

void delete(ref node2 x, int a)

	requires x::bst<n, sm, lg> & Term[n]
	ensures x'::bst<n1, s, l> & sm <= s & l <= lg & n1<=n;

{
	int tmp; 

	if (x != null)
	{
		bind x to (xval, xleft, xright) in 
		{
			if (xval == a) 
			{
				if (xright == null) {
                                        assert true;
					x = xleft; 
				}
				else
				{
					tmp = remove_min(xright);
					xval = tmp;
				}
			}
			else
			{
				if (xval < a)
					delete(xright, a);
				else
					delete(xleft, a);
			}
		}
	}
}

/*************************************************************/


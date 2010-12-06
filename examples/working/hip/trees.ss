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

/* view for trees with number of nodes */
tree1<m> == self = null & m = 0 
	or self::node2<_, p, q> * p::tree1<m1> * q::tree1<m2> & m = 1 + m1 + m2 
	inv m >= 0; 

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

/*dll1<p, S> == self = null & S = {}
	or self::node2<v, p, q> * q::dll1<self, S1> & S = union(S1, {v});*/

/* function to append 2 doubly linked lists */
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

/* function to count the number of nodes in a tree */
int count(node2 z)

	requires z::tree1<m>
	ensures z::tree1<m> & res = m & res >= 0;

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

/*void flatten1(node2 x)

	requires x::tree_1<S> 
	ensures x::dll1<null, S>;

{
	node2 tmp;

	if (x != null)
	{
		flatten1(x.left);
		flatten1(x.right);
		tmp = append1(x.left, x.right);
		x.left = null;
		x.right = tmp;
		if (tmp != null)
			tmp.left = x;
	}
}*/



/* binary search trees */

/* view for binary search trees */
bst <sm, lg> == self = null & sm <= lg 
	or (exists pl,qs: self::node2<v, p, q> * p::bst<sm, pl> * q::bst<qs, lg> & pl <= v & qs >= v)
	inv sm <= lg;

/*bst1 <S> == self = null & S = {} 
or self::node2<v, p, q> * p::bst1<S1> * q::bst1<S2> & S3 = union(S1, S2) & S = union(S3, {v}) 
& forall (a: (a notin S1 | a<=v)) & forall (b: (b notin S2 | v<=b));*/

/* insert a node in a bst */
node2 insert(node2 x, int a)

	requires x::bst<sm, lg> 
	ensures res::bst<mi, ma> & res != null & mi = min(sm, a) & ma = max(lg, a);
	
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

/*node2 insert1(node2 x, int a)
	requires x::bst1<S> 
	ensures res::bst1<S1> & res != null & S1 = union(S, {a});

{
	node2 tmp;
        node2 tmp_null = null;

	if (x == null) 
		return new node2(a, tmp_null, tmp_null);
       else 
	{
		if (a <= x.val)
		{
			//tmp = x.left;
			x.left = insert1(x.left, a);
		}
		else
		{ 
			//tmp = x.right;
			x.right = insert1(x.right, a);
		}

		return x;
	}
}*/


/* delete a node from a bst */

int remove_min(ref node2 x)

	requires x::bst<s, b> & x != null 
	ensures x'::bst<s1, b> & s <= res <= s1;

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

/*int remove_min1(ref node2 x)

	requires x::bst1<S> & x != null 
	ensures x'::bst1<S1> & forall(b : (b notin S | b >= res)) & S = union(S1, {res});

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
			tmp = remove_min1(xleft);
		}

		return tmp;
	}
}*/



void delete(ref node2 x, int a)

	requires x::bst<sm, lg> 
	ensures x'::bst<s, l> & sm <= s & l <= lg;

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

/*void delete1(ref node2 x, int a)
	requires x::bst1<S> 
	ensures x'::bst1<S1> & (a notin S | S = union(S1, {a})) 
	or (a in S | S = S1);

{
	int tmp; 

	if (x != null)
	{
		bind x to (xval, xleft, xright) in 
		{
			if (xval == a) 
			{
				if (xright == null)
					x = xleft; 
				else
				{
					tmp = remove_min1(xright);
					xval = tmp;
				}
			}
			else
			{
				if (xval < a)
					delete1(xright, a);
				else
					delete1(xleft, a);
			}
		}
	}
}*/

/*************************************************************/


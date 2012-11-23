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

tree_1<S> == self = null & S = {}
	or self::node2<v, p, q> * p::tree_1<S1> * q::tree_1<S2> & S = union(S1, S2, {v});

dll1<p, S> == self = null & S = {}
	or self::node2<v, p, q> * q::dll1<self, S1> & S = union(S1, {v});

/* function to append 2 doubly linked lists */
node2 append1(node2 x, node2 y)
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
}

/* function to transform a tree in a doubly linked list */
void flatten1(node2 x)
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
}



/* binary search trees */

/* view for binary search trees */
bst1 <S> == self = null & S = {} 
	or (exists S3: self::node2<v, p, q> * p::bst1<S1> * q::bst1<S2> & S3 = union(S1, S2) & S = union(S3, {v}) 
	& forall (a: (a notin S1 | a<=v)) & forall (b: (b notin S2 | v<=b)));

/* insert a node in a bst */
node2 insert1(node2 x, int a)
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
}

/* delete a node from a bst */
int remove_min1(ref node2 x)

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
}

void delete1(ref node2 x, int a)
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
}


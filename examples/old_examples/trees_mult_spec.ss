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
	or self::node2<_, p, q> * p::tree<m1, n1> * q::tree<m2, n2> & m = 1 + m1 + m2 & tmp = max(n1, n2) & n = 1 + tmp
	inv m >= 0 & n >= 0;

tree_1<S> == self = null & S = {}
	or self::node2<v, p, q> * p::tree_1<S1> * q::tree_1<S2> & S = union(S1, S2, {v});

tree2<m, n, S> == self = null & m = 0 & n = 0 & S = {} 
	or self::node2<v, p, q> * p::tree2<m1, n1, S1> * q::tree2<m2, n2, S2> & m = 1 + m1 + m2 & tmp = max(n1, n2) & n = 1 + tmp & S = union(S1, S2, {v})
	inv m >= 0 & n >= 0;

/* view for a doubly linked list with size */
dll<p, n> == self = null & n = 0 
	or self::node2<_, p, q> * q::dll<self, n1> & n = n1+1
	inv n >= 0;

dll1<p, S> == self = null & S = {}
	or self::node2<v, p, q> * q::dll1<self, S1> & S = union(S1, {v});
	
dll2<p, n, S> == self = null & S = {} & n = 0
  or self::node2<v, p, q> * q::dll2<q1, n-1, S1> & self = q1 & S = union(S1, {v});	

/* function to append 2 doubly linked lists */
node2 append(node2 x, node2 y)

	//********************** MULTI PRE/POST *******************************************
	requires x::dll<_, m> * y::dll<_, n>
	ensures res::dll<r, m+n>;
	
	requires x::dll1<_, S1> * y::dll1<_, S2>
	ensures res::dll1<r, S3> & S3 = union(S1, S2);
	//********************** SINGLE PRE/POST *******************************************
//	requires x::dll2<q, n1, S1> * y::dll2<p, n2, S2>
//	ensures res::dll2<_, n1+n2, S> & S = union(S1, S2);

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
	//********************** MULTI PRE/POST *******************************************
	requires x::tree<m, n> 
	ensures x::dll<null, m>;
	
	requires x::tree_1<S> 
	ensures x::dll1<null, S>;
	//********************** SINGLE PRE/POST *******************************************
//  	requires x::tree2<m, n, S> 
//	ensures x::dll2<null, m, S>;

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
bst <sm, lg> == self = null & sm <= lg 
	or self::node2<v, p, q> * p::bst<sm, pl> * q::bst<qs, lg> & pl <= v & qs >= v
	inv sm <= lg;

bst1 <S> == self = null & S = {} 
or self::node2<v, p, q> * p::bst1<S1> * q::bst1<S2> & S3 = union(S1, S2) & S = union(S3, {v})
& forall (a: (a notin S1 | a<=v)) & forall (b: (b notin S2 | v<=b));

bst2 <n, sm, lg> == self = null & sm <= lg & n = 0 
	or self::node2<v, p, q> * p::bst2<n1, sm, pl> * q::bst2<n2, qs, lg> & pl <= v & qs >= v & n = 1+n1+n2
	inv n >= 0 & sm <= lg;

bst3 <n, sm, lg, S> == self = null & sm <= lg & n = 0 & S = {}
	or self::node2<v, p, q> * p::bst3<n1, sm, pl, S1> * q::bst3<n2, qs, lg, S2> & pl <= v & qs >= v & n = 1+n1+n2 & S = union(S1, S2, {v})
	inv n >= 0 & sm <= lg;


/* insert a node in a bst */
node2 insert(node2 x, int a)
	//********************** MULTI PRE/POST *******************************************
	requires x::bst<sm, lg> 
	ensures res::bst<mi, ma> & res != null & mi = min(sm, a) & ma = max(lg, a);

  	requires x::bst1<S> 
	ensures res::bst1<S1> & S1 = union(S, {a});
	
	requires x::bst2<n, sm, lg> 
	ensures res::bst2<n+1, mi, ma> & mi = min(sm, a) & ma = max(lg, a);
	//********************** SINGLE PRE/POST *******************************************	
	//requires x::bst3<n, sm, lg, S> 
	//ensures res::bst3<n+1, mi, ma, S1> & mi = min(sm, a) & ma = max(lg, a) & S1 = union(S1, {a});
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

/************************** NOT WORKING ********************/

/* delete a node from a bst */

int remove_min(ref node2 x)
	//********************** MULTI PRE/POST *******************************************
	requires x::bst<s, b> & x != null 
	ensures x'::bst<s1, b> & s <= res <= s1;
	
	requires x::bst1<S> & x != null 
	ensures x'::bst1<S1> & forall(c : (c notin S | c >= res)) & S = union(S1, {res});

  	requires x::bst2<n, s, b> & x != null 
	ensures x'::bst2<n-1, s1, b> & s <= res <= s1;
	//********************** SINGLE PRE/POST *******************************************
//  	requires x::bst3<n, s, b, S> & x != null 
//	ensures x'::bst3<n-1, s1, b, S1> & s <= res <= s1 & S = union(S1, {res});

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
	//********************** MULTI PRE/POST *******************************************
	requires x::bst<sm, lg> 
	ensures x'::bst<s, l> & sm <= s & l <= lg;

  	requires x::bst1<S> 
	ensures x'::bst1<S1> & (a notin S | S = union(S1, {a})) 
	or (a in S | S = S1);

  	requires x::bst2<n, sm, lg> 
	ensures x'::bst2<n1, s, l> & sm <= s & l <= lg & (n1 = n | n1 = n-1);
	//********************** SINGLE PRE/POST *******************************************
//  	requires x::bst3<n, sm, lg, S> 
//	ensures x'::bst3<n1, s, l, S1> & sm <= s & l <= lg & (n1 = n | n1 = n-1) & (S = S1 | S1 = union(S, {a}));
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



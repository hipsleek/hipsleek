
data node {
	int val;
	int height;
	node left;
	node right;
}

/* view for avl trees */
avl<size, height> == self = null & size = 0 & height = 0 
	or self::node<_, height, p, q> * p::avl<size1, height1> * q::avl<size2, height2> & size = 1+size1+size2 & 
        height2<=height1+1 & height1<=height2+1 & height = max(height1, height2) + 1 
	inv size >= 0 & height >= 0;

/* function to return the height of an avl tree */
int height(node x)

	requires x::avl<m, n>
	ensures x::avl<m, n> & res = n;	

{
	if (x == null)
		return 0;
	else
		return x.height;        
}

/*  function to rotate left */
node rotate_left(node l, node rl, node rr)

	requires l::avl<lm, ln> * rl::avl<rlm, ln> * rr::avl<rrm, ln+1>
	ensures res::avl<2+lm+rlm+rrm, 2+ln>;	

{
	node tmp;
	int v = 10, h;
	
	h = height(l) + 1;
	tmp = new node(v, h, l, rl);	
	h = h + 1;
	return new node(v, h, tmp, rr);
}


/* function to rotate right */
node rotate_right(node ll, node lr, node r)

	requires ll::avl<llm, lln> * lr::avl<lrm, lln - 1> * r::avl<rm, lln - 1> 
	ensures res::avl<2 + llm + lrm + rm, 1 + lln>; 

{
	node tmp; 
	int v = 10, h;
	
	h = height(r) + 1;
	tmp = new node(v, h, lr, r);
	h = h + 1;
	return new node(v, h, ll, tmp);
}

int get_max(int a , int b)
	
	requires true 
	ensures res = max(a, b);

{
	if (a >= b)
		return a;
	else
		return b;
}


/* double left rotation */
node rotate_double_left(node a, node b, node c, node d, int v1, int v2, int v3)

	requires a::avl<am, an> * b::avl<bm, bn> * c::avl<cm, cn> * d::avl<dm, an> & an = max(bn, cn) 
	         & -1 <= bn - cn <= 1
	ensures res::avl<3 + am + bm + cm + dm, an + 2>;

{
	node tmp1, tmp2;
	int h;

	h = get_max(height(a), height(b));
	h = h + 1;
	tmp1 = new node(v1, h, a, b);

	h = get_max(height(c), height(d));
	h = h + 1;
	tmp2 = new node(v3, h, c, d);

	h = get_max(height(tmp1), height(tmp2));
	h = h + 1;
	return new node(v2, h, tmp1, tmp2);
}


/* double right rotation */
node rotate_double_right(node a, node b, node c, node d, int v1, int v2, int v3)

	requires a::avl<am, an> * b::avl<bm, bn> * c::avl<cm, cn> * d::avl<dm, an> 
	         & an = max(bn, cn) & -1 <= cn - bn <= 1
	ensures res::avl<3 + am + bm + cm + dm, 2 + an>;

{
	node tmp1, tmp2;
	int h;

	h = get_max(height(a), height(b));
	h = h + 1;
	tmp1 = new node(v3, h, a, b);

	h = get_max(height(c), height(d));
	h = h + 1;
	tmp2 = new node(v1, h, c, d);

	h = get_max(height(tmp1), height(tmp2));
	h = h + 1;
	return new node(v2, h, tmp1, tmp2);

}


node node_error() requires true ensures false;

/* function to insert a node in an avl tree (using the rotate functions) */
node insert(node x, int a)
	requires x::avl<m, n>
	ensures res::avl<m+1, _>;

{
	node tmp, tmp_null = null;

	if (x == null)
		return new node (a, 1, tmp_null, tmp_null);
	else 
	{
		if (a <= x.val)
		{
			tmp = x.left;
			x.left = insert(tmp, a);
			// check if we need rotation 
			if ((height(x.left) - height(x.right)) == 2)
			{
				if (height(x.left.left) > height(x.left.right))
				{
					return rotate_right(x.left.left, x.left.right, x.right);
				}
				else
				{
					if (height(x.left.left) == (height(x.left.right) - 1))
						return rotate_double_left(x.left.left, x.left.right.left, x.left.right.right, x.right, 1, 1, 1);
					else
						return node_error();
				}
			}
			else
			        return node_error();
		}
		else
		{
			tmp = x.right;
			x.right = insert(tmp, a);
			if ((height(x.right) - height(x.left)) == 2)
			{
				if (height(x.right.right) > height(x.right.left))
				{
					return rotate_left(x.left, x.right, x.right.right);
				}
				else
				{
					if ((height(x.right.left) - 1) == height(x.right.right))
						return rotate_double_right(x.left, x.right.left.left, x.right.left.right, x.right.right, 1, 1, 1);
					else
						return node_error();
				}
			}
			else 
				return node_error();
		}
	}
}

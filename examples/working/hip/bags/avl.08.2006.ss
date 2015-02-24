/* avl trees */

/* representation of a node in an avl tree */
data node {
	int val;
	int height;
	node left;
	node right;
}

/* view for avl trees */

/**** for omega and mona ****/
avl<m, n> == self = null & m = 0 & n = 0 
	or self::node<_, n, p, q> * p::avl<m1, n1> * q::avl<m2, n2> & m = m1+m2+1 & n3 =  max(n1-n2, n2-n1) & n3 <= 1 & tmp = max(n1, n2) & n = tmp + 1 
	inv m >= 0 & n >= 0;

avl1<n> == self = null & n = 0 
	or self::node<_, n, p, q> * p::avl1<n1> * q::avl1<n2> & n3 =  max(n1-n2, n2-n1) & n3 <= 1 & tmp = max(n1, n2) & n = tmp + 1 
	inv n >= 0;

/*avl2<n, S> == self = null & S = {} & n = 0 
	or self::node<v, n, p, q> * p::avl2<n1, S1> * q::avl2<n2, S2> & S = union(S1, S2, {v}) & n3 =  max(n1-n2, n2-n1) & n3 <= 1 & tmp = max(n1, n2) & n = tmp + 1 
	inv n >= 0;*/

/**** for isabelle */ 
/*avl<m, n> == self = null & n = 0 & m = 0
	or self::node<_, n, p, q> * p::avl<m1, n1> * q::avl<m2, n2> & n3 + n2 = n1 & n1 >= n2 & n3 <= 1 & n = n1+1 & m = m1+m2+1
	or self::node<_, n, p, q> * p::avl<m1, n1> * q::avl<m2, n2> & n3 + n2 = n1 & n1 < n2 & n3 >= -1 & n = n2+1 & m = m1+m2+1
	inv n >= 0 & m >= 0;


avl1<n> == self = null & n = 0
	or self::node<_, n, p, q> * p::avl1<n1> * q::avl1<n2> & n3 + n2 = n1 & n1 >= n2 & n3 <= 1 & n = n1+1
	or self::node<_, n, p, q> * p::avl1<n1> * q::avl1<n2> & n3 + n2 = n1 & n1 < n2 & n3 >= -1 & n = n2+1
	inv n >= 0;

avl2<n, S> == self = null & n = 0 & S = {}
	or self::node<v, n, p, q> * p::avl2<n1, S1> * q::avl2<n2, S2> & n3 + n2 = n1 & n1 >= n2 & n3 <= 1 & n = n1+1 & S = union(S1, S2, {v})
	or self::node<v, n, p, q> * p::avl2<n1, S1> * q::avl2<n2, S2> & n3 + n2 = n1 & n1 < n2 & n3 >= -1 & n = n2+1 & S = union(S1, S2, {v})
	inv n >= 0;*/

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

int height1(node x)

	requires x::avl1<n>
	ensures x::avl1<n> & res = n;	

{
	if (x == null)
		return 0;
	else
		return x.height;
}
/*
int height2(node x)

	requires x::avl2<n, S>
	ensures x::avl2<n, S> & res = n;	

{
	if (x == null)
		return 0;
	else
		return x.height;
}*/

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


node rotate_left1(node l, node rl, node rr)

	requires l::avl1<ln> * rl::avl1<ln> * rr::avl1<ln+1>
	ensures res::avl1<ln1> & ln1 = 2 + ln;	

{
	node tmp;
	int v = 10, h;
	
	h = height1(l) + 1;
	tmp = new node(v, h, l, rl);	
	h = h + 1;
	return new node(v, h, tmp, rr);
}

/*
node rotate_left2(node l, node rl, node rr)

	requires l::avl2<ln, S1> * rl::avl2<ln, S2> * rr::avl2<ln+1, S3>
	ensures res::avl2<2+ln, S>;	

{
	node tmp;
	int v = 10, h;
	
	h = height2(l) + 1;
	tmp = new node(v, h, l, rl);	
	h = h + 1;
	return new node(v, h, tmp, rr);
}*/

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

node rotate_right1(node ll, node lr, node r)

	requires ll::avl1<lln> * lr::avl1<lln - 1> * r::avl1<lln - 1> 
	ensures res::avl1<1 + lln>; 

{
	node tmp; 
	int v = 10, h;
	
	h = height1(r) + 1;
	tmp = new node(v, h, lr, r);
	h = h + 1;
	return new node(v, h, ll, tmp);
}
/*
node rotate_right2(node ll, node lr, node r)

	requires ll::avl2<lln, S1> * lr::avl2<lln-1, S2> * r::avl2<lln-1, S3>
	ensures res::avl2<lln+1, S>;//& S=union(S1, S2, S3, {10}, {10}); 

{
	node tmp; 
	int v = 10, h;
	
	h = height2(r) + 1;
	tmp = new node(v, h, lr, r);
	h = h + 1;
	return new node(v, h, ll, tmp);
}*/

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

node rotate_double_left1(node a, node b, node c, node d, int v1, int v2, int v3)

	requires a::avl1<an> * b::avl1<bn> * c::avl1<cn> * d::avl1<an> & an = max(bn, cn) 
	         & -1 <= bn - cn <= 1
	ensures res::avl1<an + 2>;

{
	node tmp1, tmp2;
	int h;

	h = get_max(height1(a), height1(b));
	h = h + 1;
	tmp1 = new node(v1, h, a, b);

	h = get_max(height1(c), height1(d));
	h = h + 1;
	tmp2 = new node(v3, h, c, d);

	h = get_max(height1(tmp1), height1(tmp2));
	h = h + 1;
	return new node(v2, h, tmp1, tmp2);
}

/*
node rotate_double_left2(node a, node b, node c, node d, int v1, int v2, int v3)

	requires a::avl2<an, S1> * b::avl2<bn, S2> * c::avl2<cn, S3> * d::avl2<an, S4> & an = max(bn, cn) 
	         & -1 <= bn - cn <= 1
	ensures res::avl2<an + 2, S> &
	S = union(S1, S2, S3, S4, {v1}, {v2}, {v3});

{
	node tmp1, tmp2;
	int h;

	h = get_max(height2(a), height2(b));
	h = h + 1;
	tmp1 = new node(v1, h, a, b);

	h = get_max(height2(c), height2(d));
	h = h + 1;
	tmp2 = new node(v3, h, c, d);

	h = get_max(height2(tmp1), height2(tmp2));
	h = h + 1;
	return new node(v2, h, tmp1, tmp2);
}*/



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


node rotate_double_right1(node a, node b, node c, node d, int v1, int v2, int v3)

	requires a::avl1<an> * b::avl1<bn> * c::avl1<cn> * d::avl1<an> 
	         & an = max(bn, cn) & -1 <= cn - bn <= 1
	ensures res::avl1<2 + an>;

{
	node tmp1, tmp2;
	int h;

	h = get_max(height1(a), height1(b));
	h = h + 1;
	tmp1 = new node(v3, h, a, b);

	h = get_max(height1(c), height1(d));
	h = h + 1;
	tmp2 = new node(v1, h, c, d);

	h = get_max(height1(tmp1), height1(tmp2));
	h = h + 1;
	return new node(v2, h, tmp1, tmp2);

}
/*
node rotate_double_right2(node a, node b, node c, node d, int v1, int v2, int v3)

	requires a::avl2<an, S1> * b::avl2<bn, S2> * c::avl2<cn, S3> * d::avl2<an, S4> 
	         & an = max(bn, cn) & -1 <= cn - bn <= 1
	ensures res::avl2<2 + an, S> & 
	S = union(S1, S2, S3, S4, {v1}, {v2}, {v3});

{
	node tmp1, tmp2;
	int h;

	h = get_max(height2(a), height2(b));
	h = h + 1;
	tmp1 = new node(v3, h, a, b);

	h = get_max(height2(c), height2(d));
	h = h + 1;
	tmp2 = new node(v1, h, c, d);

	h = get_max(height2(tmp1), height2(tmp2));
	h = h + 1;
	return new node(v2, h, tmp1, tmp2);

}
*/
/* functions to build avl trees */
node build_avl1(node x, node y)

	requires x::avl<mx, nx> * y::avl<my, nx> & x != null
	ensures res::avl<1 + mx + my, 1 + nx>;

{
	int v = 0;
	int tmp;

	tmp = x.height;
	tmp = tmp + 1;
	return new node(v, tmp, x, y);	
}

void build_avl2(node x, node y, node z)
	
	requires y::avl<my, ny> * z::avl<mz, ny> * x::node<_, _, _, _> & y != null
	ensures  x::avl<1 + my + mz, 1 + ny>;

{
	int tmp;

	x.left = y;
	x.right = z;
	x.height = y.height  + 1;
}

node node_error() requires true ensures false;

/* function to insert a node in an avl tree (using the rotate functions) */
node insert(node x, int a)
	requires x::avl<m, n>
	ensures res::avl<m1, n1> & m1 = m+1 & (n1 = n | n1 = n+1);

{
	node tmp, tmp_null = null;

	if (x == null)
		return new node (a, 1, null, null);
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
					return rotate_left(x.left, x.right.left, x.right.right);
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

node insert1(node x, int a)
	requires x::avl1<n1>
	ensures res::avl1<n2> & (n2 = n1 | n2 = n1+1);
{
	node tmp, tmp_null = null;

	if (x == null)
		return new node (a, 1, null, null);
	else 
	{
		if (a <= x.val)
		{
			tmp = x.left;
			x.left = insert1(tmp, a);
			// check if we need rotation 
			if ((height1(x.left) - height1(x.right)) == 2)
			{
				if (height1(x.left.left) > height1(x.left.right))
				{
					return rotate_right1(x.left.left, x.left.right, x.right);
				}
				else
				{
					if (height1(x.left.left) == (height1(x.left.right) - 1))
						return rotate_double_left1(x.left.left, x.left.right.left, x.left.right.right, x.right, 1, 1, 1);
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
			x.right = insert1(tmp, a);
			if ((height1(x.right) - height1(x.left)) == 2)
			{
				if (height1(x.right.right) > height1(x.right.left))
				{
					return rotate_left1(x.left, x.right.left, x.right.right);
				}
				else
				{
					if ((height1(x.right.left) - 1) == height1(x.right.right))
						return rotate_double_right1(x.left, x.right.left.left, x.right.left.right, x.right.right, 1, 1, 1);
					else
						return node_error();
				}
			}
			else 
				return node_error();
		}
	}
}
/*
node insert2(node x, int a)
	requires x::avl2<n1, S1>
	ensures res::avl2<n2, S2> & S2 = union(S1, {a}) & (n2 = n1 | n2 = n1+1);
{
	node tmp, tmp_null = null;

	if (x == null)
		return new node (a, 1, null, null);
	else 
	{
		if (a <= x.val)
		{
			tmp = x.left;
			x.left = insert2(tmp, a);
			// check if we need rotation 
			if ((height2(x.left) - height2(x.right)) == 2)
			{
				if (height2(x.left.left) > height2(x.left.right))
				{
					return rotate_right2(x.left.left, x.left.right, x.right);
				}
				else
				{
					if (height2(x.left.left) == (height2(x.left.right) - 1))
						return rotate_double_left2(x.left.left, x.left.right.left, x.left.right.right, x.right, 1, 1, 1);
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
			x.right = insert2(tmp, a);
			if ((height2(x.right) - height2(x.left)) == 2)
			{
				if (height2(x.right.right) > height2(x.right.left))
				{
					return rotate_left2(x.left, x.right.left, x.right.right);
				}
				else
				{
					if ((height2(x.right.left) - 1) == height2(x.right.right))
						return rotate_double_right2(x.left, x.right.left.left, x.right.left.right, x.right.right, 1, 1, 1);
					else
						return node_error();
				}
			}
			else 
				return node_error();
		}
	}
}
*/
/* function to insert in an avl tree (inline version) */
node insert_inline(node x, int a)

	requires x::avl<m, n> 
	ensures res::avl<m1, n1> & m1 = m+1 & (n1 = n | n1 = n+1);

{
	node k1, tmp, k2, tmp_null = null;
	int h, hl, hr, hlt;

	if (x == null)
		return new node(a, 1, tmp_null, tmp_null);
	else
	{
		if (a <= x.val)
		{	
			tmp = x.left;
			x.left = insert_inline(tmp, a);
			if ((height(x.left) - height(x.right)) == 2)
			{
				k1 = x.left;
				if (height(k1.left) > height(k1.right))
				{//SRR
					x.left = k1.right;
					h = get_max(height(k1.right), height(x.right));	
					k1.right = x; 
			
					h = h + 1;
					x.height = h;
					h = get_max(height(k1.left), h);
					h = h + 1;
					k1.height = h;
					
					return k1;					
				}
				else
				{//DLR
					if (height(k1.left) == (height(k1.right) - 1))
					{
						k2 = k1.right;
						x.left = k2.right;
						k1.right = k2.left;
						hr = height(k2.left);
						k2.left = k1; 
						hlt = height(k2.right);
						k2.right = x; 
						
						hl = height(k1.left);
						h = get_max(hl, hr);
						h = h + 1;
						k1.height = h;

						hr = height(x.right); 
						h = get_max(hlt, hr);
						h = h + 1;
						x.height = h;

						h = get_max(height(k1), x.height);
						h = h + 1;
						k2.height = h;
				
						return k2; 
					}
					else 
						return node_error();
				}
			}
			else 
				return node_error();
		}
		else	// right branch 
		{
			tmp = x.right;
			x.right = insert_inline(tmp, a);
			if ((height(x.right) - height(x.left)) == 2)
			{
				k1 = x.right;
				if (height(k1.right) > height(k1.left))
				{// SLR
					x.right = k1.left;
					hr = height(k1.left);
					k1.left = x; 

					hl = height(x.left);
					h = get_max(hr, hl);
					h = h + 1;
					x.height = h;
				
					hr = height(k1.right);
					h = get_max(height(x), hr);
					h = h + 1;
					k1.height = h;
				
					return k1;
				}
				else
				{ // DRR 
					if ((height(k1.left) - 1) == height(k1.right))
					{
						k2 = k1.left;
						
						x.right = k2.left;
						k1.left = k2.right;
						hr = height(k2.left);
						k2.left = x;
						hlt = height(k2.right);
						k2.right = k1;

						hl = height(x.left);
						h = get_max(hl, hr);
						h = h + 1;
						x.height = h;

						hr = height(k1.right);
						h = get_max(hlt, hr);	
						h = h + 1;
						k1.height = h;

						h = get_max(height(x), height(k1));
						k2.height = ++h;
					
						return k2;
					}	
					else
						return node_error();
				}				
			}
			else 
				return node_error();
		}
	}
}

node insert_inline1(node x, int a)

	requires x::avl1<n> 
	ensures res::avl1<n1> & (n1 = n | n1 = n+1);//n <= n1 <= n+1;

{
	node k1, tmp, k2, tmp_null = null;
	int h, hl, hr, hlt;

	if (x == null)
		return new node(a, 1, tmp_null, tmp_null);
	else
	{
		if (a <= x.val)
		{	
			tmp = x.left;
			x.left = insert_inline1(tmp, a);
			if ((height1(x.left) - height1(x.right)) == 2)
			{
				k1 = x.left;
				if (height1(k1.left) > height1(k1.right))
				{//SRR
					x.left = k1.right;
					h = get_max(height1(k1.right), height1(x.right));	
					k1.right = x; 
			
					h = h + 1;
					x.height = h;
					h = get_max(height1(k1.left), h);
					h = h + 1;
					k1.height = h;
					
					return k1;					
				}
				else
				{//DLR
					if (height1(k1.left) == (height1(k1.right) - 1))
					{
						k2 = k1.right;
						x.left = k2.right;
						k1.right = k2.left;
						hr = height1(k2.left);
						k2.left = k1; 
						hlt = height1(k2.right);
						k2.right = x; 
						
						hl = height1(k1.left);
						h = get_max(hl, hr);
						h = h + 1;
						k1.height = h;

						hr = height1(x.right); 
						h = get_max(hlt, hr);
						h = h + 1;
						x.height = h;

						h = get_max(height1(k1), x.height);
						h = h + 1;
						k2.height = h;
				
						return k2; 
					}
					else 
						return node_error();
				}
			}
			else 
				return node_error();
		}
		else	// right branch 
		{
			tmp = x.right;
			x.right = insert_inline1(tmp, a);
			if ((height1(x.right) - height1(x.left)) == 2)
			{
				k1 = x.right;
				if (height1(k1.right) > height1(k1.left))
				{// SLR
					x.right = k1.left;
					hr = height1(k1.left);
					k1.left = x; 

					hl = height1(x.left);
					h = get_max(hr, hl);
					h = h + 1;
					x.height = h;
				
					hr = height1(k1.right);
					h = get_max(height1(x), hr);
					h = h + 1;
					k1.height = h;
				
					return k1;
				}
				else
				{ // DRR 
					if ((height1(k1.left) - 1) == height1(k1.right))
					{
						k2 = k1.left;
						
						x.right = k2.left;
						k1.left = k2.right;
						hr = height1(k2.left);
						k2.left = x;
						hlt = height1(k2.right);
						k2.right = k1;

						hl = height1(x.left);
						h = get_max(hl, hr);
						h = h + 1;
						x.height = h;

						hr = height1(k1.right);
						h = get_max(hlt, hr);	
						h = h + 1;
						k1.height = h;

						h = get_max(height1(x), height1(k1));
						k2.height = ++h;
					
						return k2;
					}	
					else
						return node_error();
				}				
			}
			else 
				return node_error();
		}
	}
}

/*
node insert_inline2(node x, int a)
	requires x::avl2<n, S> 
	ensures res::avl2<n1, S1> & S1 = union(S, {a}) & (n1 = n | n1 = n+1);

{
	node k1, tmp, k2, tmp_null = null;
	int h, hl, hr, hlt;

	if (x == null)
		return new node(a, 1, tmp_null, tmp_null);
	else
	{
		if (a <= x.val)
		{	
			tmp = x.left;
			x.left = insert_inline2(tmp, a);
			if ((height2(x.left) - height2(x.right)) == 2)
			{
				k1 = x.left;
				if (height2(k1.left) > height2(k1.right))
				{//SRR
					x.left = k1.right;
					h = get_max(height2(k1.right), height2(x.right));	
					k1.right = x; 
			
					h = h + 1;
					x.height = h;
					h = get_max(height2(k1.left), h);
					h = h + 1;
					k1.height = h;
					
					return k1;					
				}
				else
				{//DLR
					if (height2(k1.left) == (height2(k1.right) - 1))
					{
						k2 = k1.right;
						x.left = k2.right;
						k1.right = k2.left;
						hr = height2(k2.left);
						k2.left = k1; 
						hlt = height2(k2.right);
						k2.right = x; 
						
						hl = height2(k1.left);
						h = get_max(hl, hr);
						h = h + 1;
						k1.height = h;

						hr = height2(x.right); 
						h = get_max(hlt, hr);
						h = h + 1;
						x.height = h;

						h = get_max(height2(k1), x.height);
						h = h + 1;
						k2.height = h;
				
						return k2; 
					}
					else 
						return node_error();
				}
			}
			else 
				return node_error();
		}
		else	// right branch 
		{
			tmp = x.right;
			x.right = insert_inline2(tmp, a);
			if ((height2(x.right) - height2(x.left)) == 2)
			{
				k1 = x.right;
				if (height2(k1.right) > height2(k1.left))
				{// SLR
					x.right = k1.left;
					hr = height2(k1.left);
					k1.left = x; 

					hl = height2(x.left);
					h = get_max(hr, hl);
					h = h + 1;
					x.height = h;
				
					hr = height2(k1.right);
					h = get_max(height2(x), hr);
					h = h + 1;
					k1.height = h;
				
					return k1;
				}
				else
				{ // DRR 
					if ((height2(k1.left) - 1) == height2(k1.right))
					{
						k2 = k1.left;
						
						x.right = k2.left;
						k1.left = k2.right;
						hr = height2(k2.left);
						k2.left = x;
						hlt = height2(k2.right);
						k2.right = k1;

						hl = height2(x.left);
						h = get_max(hl, hr);
						h = h + 1;
						x.height = h;

						hr = height2(k1.right);
						h = get_max(hlt, hr);	
						h = h + 1;
						k1.height = h;

						h = get_max(height2(x), height2(k1));
						k2.height = ++h;
					
						return k2;
					}	
					else
						return node_error();
				}				
			}
			else 
				return node_error();
		}
	}
}
*/
/* function to delete the smallest element in an avl tree */
int remove_min(ref node x)
	requires x::avl<m,n> & x != null
	ensures x::avl<m-1, _>;
{
	int tmp, v;

	if (x.left == null)
	{
		tmp = x.val;
		x = x.right;
		return tmp; 		
	}
	else
	{
		v = remove_min(x.left);
		
		// rebalance 
		if ((height(x.right) - height(x.left)) == 2)
		{
			if (((height(x.right.left) + 1) == height(x.right.right)) || (height(x.right.left) == height(x.right.right)))  // SLR
				x = rotate_left(x.left, x.right.left, x.right.right);   
			else                                                                                                       // DLR
				x = rotate_double_left(x.left, x.right.left.left, x.right.left.right, x.right.right, 1, 1, 1); 
		}
		
		return v;
	}
}

/* function to delete a node in a an avl tree */
void delete(ref node x, int a)

	requires x::avl<m, n> 
	ensures x'::avl<m - 1, n1>; // or if m = 0 then the same

{
	node tmp;

	if (x != null)
	{
		if (x.val == a) // x must be deleted
		{
			if (x.right == null)
				x = x.left;
			else 
			{
				tmp = x.right;
				x.val = remove_min(tmp); 
				
				//rebalance 
				if ((height(x.left) - height(x.right)) == 2)
				{
					if (((height(x.left.left) - 1) == height(x.left.right)) || (height(x.left.left) == height(x.left.right)))
						x = rotate_right(x.left.left, x.left.right, x.right); // SRR
					else 
						x = rotate_double_right(x.left.left, x.left.right.left, x.left.right.right, x.right, 1, 1, 1); // DRR
				}
			}
		}
		else 
			if (x.val < a)
			{
				delete(x.right, a);

				//rebalance
				if ((height(x.left) - height(x.right)) == 2)
				{
					if (((height(x.left.left) - 1) == height(x.left.right)) || (height(x.left.left) == height(x.left.right)))
						x = rotate_right(x.left.left, x.left.right, x.right); // SRR
					else 
						x = rotate_double_right(x.left.left, x.left.right.left, x.left.right.right, x.right,1 ,1, 1); // DRR
				}
				
			}
			else 	
			{
				delete(x.left, a);
				
				// rebalance 
				if ((height(x.right) - height(x.left)) == 2)
				{
					if (((height(x.right.left) + 1) == height(x.right.right)) || (height(x.right.left) == height(x.right.right)))  // SLR
						x = rotate_left(x.left, x.right.left, x.right.right);   
					else                                                                                                       // DLR
						x = rotate_double_left(x.left, x.right.left.left, x.right.left.right, x.right.right, 1, 1, 1);
				}

			}
	}
}



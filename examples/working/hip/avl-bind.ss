/* avl trees */

/* representation of a node in an avl tree */
data node {
	int val;
	int height;
	node left;
	node right;
}

/* view for avl trees */
avl<m, n> == self = null & m = 0 & n = 0 
	or self::node<_, n, p, q> * p::avl<m1, n1> * q::avl<m2, n2> & m = 1+m1+m2 & -1 <= n1-n2 <=1 & n = max(n1, n2) + 1 
	inv m >= 0 & n >= 0;

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
	ensures res::avl<m+1, _>;

{
	node tmp, tmp_null = null;

	if (x == null)
		return new node (a, 1, tmp_null, tmp_null);
	else 
	{
	bind x to (xval, xheight, xleft, xright) in {
		if (a <= xval)
		{
			tmp = xleft;
			xleft = insert(tmp, a);
			// check if we need rotation 
			if ((height(xleft) - height(xright)) == 2)
			{
			bind xleft to (xleftval, xleftheight, xleftleft, xleftright) in {
				if (height(xleftleft) > height(xleftright))
				{
					return rotate_right(xleftleft, xleftright, xright);
				}
				else
				{
					if (height(xleftleft) == (height(xleftright) - 1))
						return rotate_double_left(xleftleft, xleftright.left, xleftright.right, xright, 1, 1, 1);
					else
						return node_error();
				}
			}
			}
			else
			        return node_error();
		}
		else
		{
			tmp = xright;
			xright = insert(tmp, a);
			if ((height(xright) - height(xleft)) == 2)
			{
			bind xright to (xrightval, xrightheight, xrightleft, xrightright) in {
				if (height(xrightright) > height(xrightleft))
				{
					return rotate_left(xleft, xrightleft, xrightright);
				}
				else
				{
					if ((height(xrightleft) - 1) == height(xrightright))
						return rotate_double_right(xleft, xrightleft.left, xrightleft.right, xrightright, 1, 1, 1);
					else
						return node_error();
				}
			}
			}
			else 
				return node_error();
		}
	}
	}
}
/*
/* function to insert in an avl tree (inline version) */
node insert_inline(node x, int a)

	requires x::avl<m, n> 
	ensures res::avl<m + 1, n1> & n <= n1 <= n+1;

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


/* function to delete the smallest element in an avl tree */
int remove_min(node@R x)
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
void delete(node@R x, int a)

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
*/


data node {
	int val;
	int color; /*  0 for black, 1 for red */
	node left;
	node right;
}


/* view for red-black trees (internal node) */
rb<n, cl, bh> == self = null & n = 0 & bh = 1 & cl = 0 
	or self::node<v, 1, l, r> * l::rb<nl, 0, bhl> * r::rb<nr, 0, bhr> & cl = 1 & n = 1 + nl + nr & bhl = bh & bhr = bh
	or self::node<v, 0, l, r> * l::rb<nl, _, bhl> * r::rb<nr, _, bhr> & cl = 0 & n = 1 + nl + nr & bhl = bhr & bh = 1 + bhl
	inv n >= 0 & bh >= 1 & 0 <= cl <= 1;

/* view for red-black trees (root) */
rb2<n, bh> == self = null  & bh = 1 & n = 0
	or self::node<_, 0, l, r> * l::rb<nl, cl, bhl> * r::rb<nr, cr, bhr> & bhl = bhr & bh = 1 + bhl & n = nl + nr + 1
	inv n>=0 & bh >= 1;


/* function to check if a node is red */
bool is_red(node x)
	
	requires x::rb<n, cl, bh>
	ensures x::rb<n, cl, bh> & cl = 1 & res
		or x::rb<n, cl, bh> & cl = 0 & !res;

{
	if (x == null)
		return false; 
	else 
		if (x.color == 0) 
			return false;
		else
			return true;
}

/* function to check if a node is black */
bool is_black(node x)

	requires x::rb<n, cl, bh>
	ensures x::rb<n, cl, bh> & cl = 1 & !res
		or x::rb<n, cl, bh> & cl = 0 & res;

{
	if (x == null)
		return true; 
	else
 
		if (x.color == 0) 
			return true;
		else
			return false;
}

/* simple right rotation */
node rotate_right(node k1)
	
	requires k1::node<v, 0, l, r> * r::rb<nr, 0, bhr> *l::node<_, 1, ll, lr> * ll::rb<nll, 1, bhll> * lr::rb<nlr, 0, bhlr> & bhlr = bhr & bhr = bhll
	ensures res::rb<nr+nll+nlr+2, 0, bhr+1>;

{
	node k2 = k1.left; 
	k1.left = k2.right;
	k2.right = k1;

	// update colors 
	k2.color = 0; 
	k2.right.color = 1; 
	
	return k2;
}

/* simple right rotation */
node rotate_rightd(node k1)
	
	requires k1::node<vk1, 1, l, r> * r::rb<nr, 0, bhr> * l::node<vl, 1, ll, lr> * ll::rb<nll, 0, bhll> * lr::rb<nlr, 0, bhlr> & bhr = bhlr & bhlr = bhll
	ensures res::node<vl, 1, lres, rres> * lres::rb<nll, 0, bhll> * rres::rb<nr+nlr+1, 1, bhr>;

{
	node k2 = k1.left; 
	k1.left = k2.right;
	k2.right = k1;
	
	return k2;
}



/* simple left rotation */
node rotate_left(node k1)
	
	requires k1::node<v, 0, l, r> * l::rb<nl, 0, bhl> * r::node<_, 1, rl, rr> * rl::rb<nrl, 0, bhrl> * rr::rb<nrr, 1, bhrr> & bhl = bhrl & bhrl = bhrr
	ensures res::rb<nl+nrl+nrr+2, 0, bhl + 1>;

{
	node k2 = k1.right; 
	k1.right = k2.left;
	k2.left = k1;

	// update colors 
	k2.color = 0;                             
	k2.left.color = 1; 
	
	return k2;
}

/* simple left rotation - double rotation */
node rotate_leftd(node k1)
	
	requires k1::node<vk1, 1, l, r> * l::rb<nl, 0, bhl> * r::node<vr, 1, rl, rr> * rl::rb<nrl, 0, bhrl> * rr::rb<nrr, 0, bhrr> & bhl = bhrl & bhrl = bhrr
	ensures res::node<vr, 1, lres, rres> * lres::rb<nl+nrl+1, 1, bhl> * rres::rb<nrr, 0, bhrr>;

{
	node k2 = k1.right; 
	k1.right = k2.left;
	k2.left = k1;

	return k2;
}


/* double left rotation */
node double_rotate_left(node k1)
	requires k1::node<vk1, 0, l, r> * l::node<vl, 1, ll, lr> * ll::rb<nll, 0, bhll> * lr::rb<nlr, 1, bhlr> * r::rb<nr, 0, bhr> & 
		 bhll = bhlr & bhlr = bhr
	ensures res::rb<nll + nlr + nr + 2, 0, bhll+1>;
{
	k1.left  = rotate_leftd(k1.left); 
	
	return rotate_right(k1);
}


/* double right rotation */
node double_rotate_right(node k1)
	requires k1::node<vk1, 0, l, r> * l::rb<nl, 0, bhl> * r::node<vr, 1, rl, rr> * rl::rb<nrl, 1, bhrl> * rr::rb<nrr, 0, bhrr> & bhl = bhrl & bhrl = bhrr
	ensures res::rb<nrl + nl + nrr + 2, 0, bhl+1>;
{
	k1.right  = rotate_rightd(k1.right); 
	
	return rotate_left(k1);
}
/*
/* insert a node in a red black tree */
node insert(node x, int v) 
	requires x::rb<n, _, bh> 
	ensures res::rb<n+1, _, bhres> & bh <= bhres <= bh+1;
{
	node tmp = null;

	if (x == null) 
		return new node(v, 1, tmp, tmp);
	else
	{
		if (v < x.val) 
		{
			x.left = insert(x.left, v);

			// rebalance
			if (x.color == 0)
			{
				// parent red
				if (is_red(x.left))
					// uncle red
					if (is_red(x.right))
					{
						//recolor
						if (is_red(x.left.left) || is_red(x.left.right))
						{
							x.color = 1;
							x.left.color = 0;
							x.right.color = 0;
						}
					}
					// uncle black
					else
					{
						if (is_red(x.left.left))
						{
							//simple right rotation 
							x = rotate_right(x);
						}
						else
							if (is_red(x.left.right))
							{
								//double rotation 
								x = double_rotate_left(x);
							}
														
					}
			}

		}
		else
		{
			x.right = insert(x.right, v);
			
			//rebalance
			if (x.color == 0)
			{
				// parent red
				if (is_red(x.right))
					// uncle red
					if (is_red(x.left))
					{
						//recolor 
						if (is_red(x.right.left) || is_red(x.right.right))
						{
							x.color = 1; 
							x.left.color = 0; 
							x.right.color = 0; 
						}

					}
					// uncle black
					else 
					{
						if (is_red(x.right.right))
						{
							//simple left rotation 
							x = rotate_left(x);
						}
						else
							if (is_red(x.right.left))
							{
								//double rotation 
								x = double_rotate_right(x);
							}
					}
			}

			
		}
		
		return x;
	}
} 
*/
node insert(node x, int v)

	requires x::rb<n, _, bh>
	ensures res::rb<n+1, _, bh1> & res != null & bh<=bh1<=bh;

{
	node tmp, tmp_null = null;

	if (x == null)	

		return new node(v, 1, tmp_null, tmp_null);
	else 
	{
		if (v <= x.val)
		{ // left
			tmp = x.left;
			x.left = insert(tmp, v);
	
			// rebalance 
			if (x.color == 0)
			{
				if (is_red(x.left))
				{
					if (is_red(x.left.left))
					{
						if (is_red(x.right))
						{
							x.left.color = 0;
							x.right.color = 0;
							return x;
						}
						else 
						{
							x = rotate_right(x);
							return x;
						}
					}
					else 
					{
						if (is_red(x.left.right))
						{
							if (is_red(x.right))
							{
								x.left.color = 0;
								x.right.color = 0;
								return x;
							}
							else 
							{
								x = double_rotate_left(x);
								return x;
							}
						}
						else
							return node_error();
					}
				}
				else
					return node_error();
			}
			else 
				return node_error();
		}
		else 
		{ // right
			tmp = x.right;
			x.right = insert(tmp, v);

			// rebalance
			if (x.color == 0)
			{
				if (is_red(x.right))
				{
					if (is_red(x.right.left))
						if (is_red(x.left))
						{
							x.left.color = 0;
							x.right.color = 0; 
							return x;
						}
						else 
						{
							x =  double_rotate_right(x);
							return x;
						}
					else
					{
						if (is_red(x.right.right))
							if (is_red(x.left))
							{	
								x.left.color = 0;
								x.right.color = 0;
								return x; 
							}
							else
							{
								x = rotate_left(x);
								return x;
							}
						else
							return node_error();
					}
				}
				else
					return node_error();
			}
			else 
				return node_error();
		}
	}
}

node node_error() requires true ensures false;

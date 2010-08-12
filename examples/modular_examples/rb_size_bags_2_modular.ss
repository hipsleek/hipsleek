/* red black trees */

data node {
	int val;
	int color; /*  0 for black, 1 for red */
	node left;
	node right;
}

/* view for red-black trees */
/*
rb1<cl, "h":bh, "n":n, "S":S> == 
	self = null & cl = 0 & ["h":bh = 1; "n":n = 0; "S":S={}] or
	self::node<v, 1, l, r> * l::rb1<0, bhl, n1> * r::rb1<0, bhr, n2> & cl = 1 & ["h":bhl = bh & bhr = bh; "n":n=n1+n2+1; "S":S=union(S1, S2, {v})] or
	self::node<v, 0, l, r> * l::rb1<_, bhl, S1> * r::rb1<_, bhr, S2> & cl = 0 & ["h":bhl = bhr & bh = 1 + bhl; "n":n=n1+n2+1; "S":S=union(S1, S2, {v})]
	inv 0 <= cl <= 1 & ["h":bh >= 1; "n"n >= 0];
*/
rb1<cl, bh, n, S> == self = null & n=0 & bh = 1 & cl = 0 & S={}
	or self::node<v, 1, l, r> * l::rb1<0, bhl, nl, S1> * r::rb1<0, bhr, nr, S2> & cl = 1 & n = 1 + nl + nr & bhl = bh & bhr = bh & S=union(S1, S2, {v})
	or self::node<v, 0, l, r> * l::rb1<_, bhl, nl, S1> * r::rb1<_, bhr, nr, S2> & cl = 0 & n = 1 + nl + nr & bhl = bhr & bh = 1 + bhl & S=union(S1, S2, {v})
	inv 0 <= cl <= 1 & ["h":bh >= 1; "n": n >= 0];

/* rotation case 3 */
node rotate_case_3_1(node a, node b, node c, int v1, int v2)

	requires a::rb1<1, bha, n1, S1> * b::rb1<0, bhb, n2, S2> * c::rb1<0, bhc, n3, S3> & ["h":bha=bhb & bha=bhc]
	ensures res::rb1<0, bh, n, S> & ["h":bh=bha+1; "n":n=n1+n2+n3+2; "S":S = union(S1, S2, S3, {v1, v2})];

{
	node tmp;

	tmp = new node(v2, 1, b, c);
	
	return new node(v1, 0, a, tmp);
}

/* rotation to transform case 2 in case 3, then apply case 3 */
node case_2_1(node a, node b, node c, node d, int v1, int v2, int v3)
	requires a::rb1<0, bha, n1, S1> * b::rb1<0, bhb, n2, S2> * c::rb1<0, bhc, n3, S3> * d::rb1<0, bhd, n4, S4> & ["h":bha=bhb & bha=bhc & bha=bhd]
	ensures res::rb1<0, bh, n, S> & ["h":bh=bha+1; "n":n=n1+n2+n3+n4+3; "S":S = union(S1, S2, S3, S4, {v1, v2, v3})];

{
	node tmp;

	tmp = new node(v1, 1, a, b);

	return  rotate_case_3_1(tmp, c, d, v2, v3);
}

/* RIGHT */
/* rotation case 3 */
node rotate_case_3r_1(node a, node b, node c, int v1, int v2)

	requires a::rb1<0, bha, n1, S1> * b::rb1<0, bha, n2, S2> * c::rb1<1, bha, n3, S3>
	ensures res::rb1<0, bha + 1, n, S> & n=n1+n2+n3+2 & S = union(S1, S2, S3, {v1, v2});

{
	node tmp;

	tmp = new node(v1, 1, a, b);
	
	return new node(v2, 0, tmp, c);
}


/* rotation to transform case 2 in case 3, then apply case 3 */
node case_2r_1(node a, node b, node c, node d, int v1, int v2, int v3)
	
	requires a::rb1<0, bha, n1, S1> * b::rb1<0, bha, n2, S2> * c::rb1<0, bha, n3, S3> * d::rb1<0, bha, n4, S4>
	ensures res::rb1<0, bha + 1, n, S> & n=n1+n2+n3+n4+3 & S = union(S1, S2, S3, S4, {v1, v2, v3});

{
	node tmp;

	tmp = new node(v3, 1, c, d);

	return rotate_case_3r_1(a, b, tmp, v1, v2);
}

/* function to check if a node is red */
bool is_red_1(node x)
	
	requires x::rb1<cl, bh, n, S>
	ensures x::rb1<cl, bh, n, S> & cl = 1 & res
		or x::rb1<cl, bh, n, S> & cl = 0 & !res;

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
bool is_black_1(node x)

	requires x::rb1<cl, bh, n, S>
	ensures x::rb1<cl, bh, n, S> & cl = 1 & !res
		or x::rb1<cl, bh, n, S> & cl = 0 & res;

{
	if (x == null)
		return true; 
	else
 
		if (x.color == 0) 
			return true;
		else
			return false;
}

/* function for case 6 delete (simple rotation) */
node del_6_1(node a, node b, node c, int color, int v1, int v2)

	requires a::rb1<0, ha, n1, S1> * b::rb1<_, hb, n2, S2> * c::rb1<1, hc, n3, S3> & color = 0 & ["h":ha=hb & ha=hc] or 
		 a::rb1<0, ha, n1, S1> * b::rb1<_, hb, n2, S2> * c::rb1<1, hc, n3, S3> & color = 1 & ["h":ha=hb & ha=hc] 
	ensures res::rb1<0, h, n, S> & color = 0 & ["h":h=ha+2; "n":n=n1+n2+n3+2; "S":S = union(S1, S2, S3, {v1, v2})] or 
		res::rb1<1, h, n, S> & color = 1 & ["h":h=ha+1; "n":n=n1+n2+n3+2; "S":S = union(S1, S2, S3, {v1, v2})];
{
	node tmp; 

	c.color = 0;

	tmp = new node(v1, 0, a, b);

	return new node(v2, color, tmp, c);
}

/* function for case 6 at delete (simple rotation) - when is right child */
node del_6r_1(node a, node b, node c, int color, int v1, int v2)

	requires a::rb1<1, ha, n1, S1> * b::rb1<_, ha, n2, S2> * c::rb1<0, ha, n3, S3> & color = 0 or 
		 a::rb1<1, ha, n1, S1> * b::rb1<_, ha, n2, S2> * c::rb1<0, ha, n3, S3> & color = 1
	ensures res::rb1<0, ha + 2, n, S> & n=n1+n2+n3+2 & S = union(S1, S2, S3, {v1, v2}) & color = 0 or 
		res::rb1<1, ha + 1, n, S> & n=n1+n2+n3+2 & S = union(S1, S2, S3, {v1, v2}) & color = 1;

{
	node tmp;
	
	a.color = 0;
	
	tmp = new node(v2, 0, b, c);

	return new node(v1, color, a, tmp);	
}

/* function for case 5 (double rotation) */
node del_5_1(node a, node b, node c, node d, int color, int v1, int v2, int v3)

	requires a::rb1<0, ha, n1, S1> * b::rb1<0, hb, n2, S2> * c::rb1<0, hc, n3, S3> * d::rb1<0, hd, n4, S4> & color = 0 & ["h":ha=hb & ha=hc & ha=hd] or 
		 a::rb1<0, ha, n1, S1> * b::rb1<0, hb, n2, S2> * c::rb1<0, hc, n3, S3> * d::rb1<0, hd, n4, S4> & color = 1 & ["h":ha=hb & ha=hc & ha=hd]
	ensures res::rb1<0, h, n, S>  & color = 0 & ["h":h=ha+2; "n":n=n1+n2+n3+n4+3; "S":S = union(S1, S2, S3, S4, {v1, v2, v3})] or 
		res::rb1<1, h, n, S> & color = 1 & ["h":h=ha+1; "n":n=n1+n2+n3+n4+3; "S":S = union(S1, S2, S3, S4, {v1, v2, v3})];

{
	node tmp;
	
	tmp = new node(v3, 1, c, d);

	return del_6_1(a, b, tmp, color, v1, v2);
}


/* function for case 5(double rotation) - right child */
node del_5r_1(node a, node b, node c, node d, int color, int v1, int v2, int v3)
	requires a::rb1<0, h, n1, S1> * b::rb1<0, h, n2, S2> * c::rb1<0, h, n3, S3> * d::rb1<0, h, n4, S4> & color = 0 or 
		 a::rb1<0, h, n1, S1> * b::rb1<0, h, n2, S2> * c::rb1<0, h, n3, S3> * d::rb1<0, h, n4, S4> & color = 1 
	ensures res::rb1<0, h + 2, n, S> & n=n1+n2+n3+n4+3 & S = union(S1, S2, S3, S4, {v1, v2, v3}) & color = 0 or 
		res::rb1<1, h + 1, n, S> & n=n1+n2+n3+n4+3 & S = union(S1, S2, S3, S4, {v1, v2, v3}) & color = 1;
{
	node tmp;

	tmp = new node(v1, 1, a, b);

	return del_6r_1(tmp, c, d, color, v2, v3);
}

/* function for case 4(just recolor) */
node del_4_1(node a, node b, node c, int v1, int v2)
	requires a::rb1<0, ha, n1, S1> * b::rb1<0, hb, n2, S2> * c::rb1<0, hc, n3, S3> & ["h":ha=hb & ha=hc] 
	ensures res::rb1<0, h, n, S> & ["h":h=ha+1; "n":n=n1+n2+n3+2; "S":S = union(S1, S2, S3, {v1, v2})];

{
	node tmp; 

	tmp = new node(v2, 1, b, c);
	
	return new node(v1, 0, a, tmp);
}


/* function for case 4 (just recolor) - right child */
node del_4r_1(node a, node b, node c, int v1, int v2)

	requires a::rb1<0, ha, n1, S1> * b::rb1<0, ha, n2, S2> * c::rb1<0, ha, n3, S3>  
	ensures res::rb1<0, ha + 1, n, S> & n=n1+n2+n3+2 & S = union(S1, S2, S3, {v1, v2});

{
	node tmp; 

	tmp = new node(v1, 1, a, b);

	return new node(v2, 0, tmp, c);
}

/* function for case 3 (just recolor) */
node del_3_1(node a, node b, node c, int v1, int v2)
	requires a::rb1<0, ha, n1, S1> * b::rb1<0, hb, n2, S2> * c::rb1<0, hc, n3, S3> & ["h":ha=hb & ha=hc]  
	ensures res::rb1<0, h, n, S> & ["h":h=ha+1; "n":n=n1+n2+n3+2; "S":S = union(S1, S2, S3, {v1, v2})];
{
	node tmp;

	tmp = new node(v2, 1, b, c);
	
	return new node(v1, 0, a, tmp);
}

/* function for case 3 (just recolor) - right child */
node del_3r_1(node a, node b, node c, int v1, int v2)

	requires a::rb1<0, ha, n1, S1> * b::rb1<0, ha, n2, S2> * c::rb1<0, ha, n3, S3>   
	ensures res::rb1<0, ha + 1, n, S> & n=n1+n2+n3+2 & S = union(S1, S2, S3, {v1, v2});

{
	node tmp;

	tmp = new node(v1, 1, a, b);

	return new node(v2, 0, tmp, c);
}

/* function for case 2 (simple rotation + applying one of the cases 4, 5, 6) */
node del_2_1(node a, node b, node c, int v1, int v2)
	//requires a::rb1<0, ha, n1, S1> * b::rb1<0, hb, n2, S2> * c::rb1<0, hc, n3, S3> & b != null & c != null & ["h":hb=ha+1 & hc=ha+1]
	//ensures res::rb1<0, h, n, S> & ["h":h=ha+2; "n":n=n1+n2+n3+2; "S":S = union(S1, S2, S3, {v1, v2})];
	requires a::rb1<0, ha, n1, S1> * b::node<vb, 0, bl, br> * bl::rb1<_, hbl, nbl, Sbl> * br::rb1<_, hbr, nbr, Sbr> * c::rb1<0, hc, n3, S3> & bl != null & c != null & ["h":hbl=ha & hbr=ha & hc=ha+1]
	ensures res::rb1<0, h, n, S> & ["h":h=ha+2; "n":n=n1+n2+n3+2; "S":S = union(S1, Sbl, Sbr, S3, {v1, v2, vb})];

{
	node tmp; 
	node tmp1;
	node tmp2;

	if (is_black_1(b.right))
	{
		if (is_black_1(b.left)) {
			assume false;
			tmp = del_4_1(a, b.left, b.right, v1, b.val);
		} else { 
			//assume false;
			//assume bl::node<vbl, 1, bll, blr> * bll::rb1<_, hbll, nbll, Sbll> * blr::rb1<_, hblr, nblr, Sblr> & ["b":Sbl=union(Sbll, Sblr, {vbl})];
			tmp = del_5_1(a, b.left.left, b.left.right, b.right, 1, v1, b.left.val, b.val);
			
			//tmp1 = new node(b.val, 1, b.left.right, b.right);
			////tmp = del_6_1(a, b.left.left, tmp1, 1, v1, b.left.val);
			//tmp1.color = 0;
			//tmp2 = new node(v1, 0, a, b.left.left);
			//tmp = new node(b.left.val, 1, tmp2, tmp1);
		}
	} else { 
		assume false;
		tmp = del_6_1(a, b.left, b.right, 1, v1, b.val);
	}
	return new node(v2, 0, tmp, c);
}

node del_2r_1(node a, node b, node c, int v1, int v2)

	requires a::rb1<0, h+1, n1, S1> * b::rb1<0, h+1, n2, S2> * c::rb1<0, h, n3, S3> & b != null //& a != null
	ensures res::rb1<0, h + 2, n, S> & n=n1+n2+n3+2 & S = union(S1, S2, S3, {v1, v2});

{
	node tmp, f; 

	if (is_black_1(b.left))
	{
		if (is_black_1(b.right))
			tmp = del_4r_1(b.left, b.right, c, b.val, v2);
		else 
			tmp = del_5r_1(b.left, b.right.left, b.right.right, c, 1, b.val, b.right.val, v2);
	}
	else 
		tmp = del_6r_1(b.left, b.right, c, 1, b.val, v2);
	f = new node(v1, 0, a, tmp);	
	return f;
}

int bh(node x) requires true ensures false;

/* function to delete the smalles element in a rb and then rebalance */
int remove_min_1(ref node x)

	requires x::rb1<cl, bh, n1, S1> & x != null & 0 <= cl <= 1
	ensures x'::rb1<cl2, bh, n2, S2> & n2=n1-1 & S1 = union(S2, {res}) & cl = 1 & 0 <= cl2 <= 1 or
		x'::rb1<0, bh2, n3, S3> & n3=n1-1 & S1 = union(S3, {res}) & bh-1 <= bh2 <= bh & cl = 0;

{
	int v1;

	if (x.left == null)
	{
		int tmp = x.val;

		if (is_red_1(x.right))
			x.right.color = 0; 
		x = x.right;
	
		return tmp;
	}
	else 
	{
		v1 = remove_min_1(x.left);

		//rebalance 
		if (bh(x.left) < bh(x.right))
		{
			if (is_black_1(x.left))
			{
				if (is_red_1(x.right))
				{
					if (x.right.left != null)
                                        {
						x = del_2_1(x.left, x.right.left, x.right.right, x.val, x.right.val);
						//assume false;
                                                return v1;
                                        }
					else
						return v1;
				}
				else 
				{
					if (is_black_1(x.right.right))
					{
						if (is_black_1(x.right.left))
							if (x.color == 0)
							{
								x = del_3_1(x.left, x.right.left, x.right.right, x.val, x.right.val);
								return v1;
							}	
							else
							{
								x = del_4_1(x.left, x.right.left, x.right.right, x.val, x.right.val);
								return v1;
							}
						else
						{
							x = del_5_1(x.left, x.right.left.left, x.right.left.right, x.right.right, x.color, x.val, x.right.left.val, x.right.val);
							return v1;
						}
					}
					else
					{
						x = del_6_1(x.left, x.right.left, x.right.right, x.color, x.val, x.right.val);
						return v1; 
					}
							
				}
			}
			else 
				return v1;
		}
		else 
			return v1;
	}
}

/* function to delete an element in a red black tree */
void del_1(ref node  x, int a)
	requires x::rb1<cl, bh, n1, S1> & 0 <= cl <= 1
	ensures  
	x'::rb1<cl2, bh, n2, S2> & n1=n2+1 & S1 = union(S2, {a}) & cl = 1 & 0 <= cl2 <= 1 or
	x'::rb1<0, bh2, n2, S2> & n1=n2+1 & S1 = union(S2, {a}) & bh-1 <= bh2 <= h & cl = 0 or
	x'::rb1<cl, bh, n1, S1>;

{
	int v;

	if (x != null)
	{
		if (x.val == a) // delete x
		{
			if (x.right == null)
			{
				if (is_red_1(x.left))
					x.left.color = 0;
				x = x.left;

			}
			else 
			{
				v = remove_min_1(x.right);
				if (bh(x.right) < bh(x.left))
				{
					if (is_black_1(x.right))
					{
						if (is_red_1(x.left))	
						{
							if (x.left.right != null)
								x = del_2r_1(x.left.left, x.left.right, x.right, x.left.val, x.val);
						}
						else 
						{
							if (is_black_1(x.left.left))
								if (is_black_1(x.left.right))
									if (x.color == 0)
										x = del_3r_1(x.left.left, x.left.right, x.right, x.left.val, x.val);
									else
										x = del_4r_1(x.left.left, x.left.right, x.right, x.left.val, x.val);
								else 
									x = del_5r_1(x.left.left, x.left.right.left, x.left.right.right, x.right, x.color, x.left.val, x.left.right.val, x.val);
							else
								x = del_6r_1(x.left.left, x.left.right, x.right, x.color, x.left.val, x.val);
						}
								
					}
				}		
			}
		}
		else 
		{
			if (x.val < a) //go right 
			{
				del_1(x.right, a);

				// rebalance
				if (bh(x.right) < bh(x.left))
				{
					if (is_black_1(x.right))
						if (is_red_1(x.left))
						{
							if (x.left.right != null)
								x = del_2r_1(x.left.left, x.left.right, x.right, x.left.val, x.val);
						}
						else 	

						{
							if (is_black_1(x.left.left))
								if (is_black_1(x.left.right))
									if (x.color == 0)
										x = del_3r_1(x.left.left, x.left.right, x.right, x.left.val, x.val);
									else 
										x = del_4r_1(x.left.left, x.left.right, x.right, x.left.val, x.val);
								else 
									x = del_5r_1(x.left.left, x.left.right.left, x.left.right.right, x.right, x.color, x.left.val, x.left.right.val, x.val);
							else 
								x = del_6r_1(x.left.left, x.left.right, x.right, x.color, x.left.val, x.val);
						}
				}
			}
			else   // go left 
			{
				del_1(x.left, a);

				// rebalance 
				if (bh(x.left) < bh(x.right))
				{
					if (is_black_1(x.left))
						if (is_red_1(x.right))
						{
							if (x.right.left != null)
								x = del_2_1(x.left, x.right.left, x.right.right, x.val, x.right.val);			
						}
						else 
						{
							if (is_black_1(x.right.right))
								if (is_black_1(x.right.left))
								{
									if (x.color == 0)
										x = del_3_1(x.left, x.right.left, x.right.right, x.val, x.right.val);
									else
										x = del_4_1(x.left, x.right.left, x.right.right, x.val, x.right.val);
								}
								else
									x = del_5_1(x.left, x.right.left.left, x.right.left.right, x.right.right, x.color, x.val, x.right.left.val, x.right.val);

							else 
								x = del_6_1(x.left, x.right.left, x.right.right, x.color, x.val, x.right.val);	
						}
				}
			}
		}
	}
}

node node_error() requires true ensures false; 

node insert_1(node x, int v)
	requires x::rb1<_, bh, n, S>
	ensures res::rb1< _, bh1, n1, S1> & res != null & bh <= bh1 <= bh & n1=n+1 & S1 = union(S, {v});

{
	node tmp, tmp_null = null;

	if (x == null)	

		return new node(v, 1, tmp_null, tmp_null);
	else 
	{
		if (v <= x.val)
		{ // left
			tmp = x.left;
			x.left = insert_1(tmp, v);
	
			// rebalance 
			if (x.color == 0)
			{
				if (is_red_1(x.left))
				{
					if (is_red_1(x.left.left))
					{
						if (is_red_1(x.right))
						{
							x.left.color = 0;
							x.right.color = 0;
							return x;
						}
						else 
						{
							x = rotate_case_3_1(x.left.left, x.left.right, x.right, x.left.val, x.val);
							return x;
						}
					}
					else 
					{
						if (is_red_1(x.left.right))
						{
							if (is_red_1(x.right))
							{
								x.left.color = 0;
								x.right.color = 0;
								return x;
							}
							else 
							{
								x = case_2_1(x.left.left, x.left.right.left, x.left.right.right, x.right, x.left.val, x.left.right.val, x.val);
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
			x.right = insert_1(tmp, v);

			// rebalance
			if (x.color == 0)
			{
				if (is_red_1(x.right))
				{
					if (is_red_1(x.right.left))
						if (is_red_1(x.left))
						{
							x.left.color = 0;
							x.right.color = 0; 
							return x;
						}
						else 
						{
							x = case_2r_1(x.left, x.right.left.left, x.right.left.right, x.right.right, x.val, x.right.left.val, x.right.val);
							return x;
						}
					else
					{
						if (is_red_1(x.right.right))
							if (is_red_1(x.left))
							{	
								x.left.color = 0;
								x.right.color = 0;
								return x; 
							}
							else
							{
								x = rotate_case_3r_1(x.left, x.right.left, x.right.right, x.val, x.right.val);
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

/****************************************************************************/



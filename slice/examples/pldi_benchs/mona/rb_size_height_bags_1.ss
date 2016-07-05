/* red black trees */

data node {
	int val;
	int color; /*  0 for black, 1 for red */
	node left;
	node right;
}

/* view for red-black trees */
rb1<cl, bh, S> == self = null & bh = 1 & cl = 0 & S={}
	or self::node<v, 1, l, r> * l::rb1<0, bhl, S1> * r::rb1<0, bhr, S2> & cl = 1 & bhl = bh & bhr = bh & S = union(S1, S2, {v})
	or self::node<v, 0, l, r> * l::rb1<_, bhl, S1> * r::rb1<_, bhr, S2> & cl = 0 & bhl = bhr & bh = 1 + bhl & S = union(S1, S2, {v})
	inv bh >= 1 & 0 <= cl <= 1;

/* rotation case 3 */
node rotate_case_3_1(node a, node b, node c)

	requires a::rb1<1, bha, S1> * b::rb1<0, bha, S2> * c::rb1<0, bha, S3> 
	ensures res::rb1<0, bha + 1, S4> & S4 = union(S1, S2, S3, {0}, {0});

{
	node tmp;

	tmp = new node(0, 1, b, c);
	
	return new node(0, 0, a, tmp);
}


/* rotation to transform case 2 in case 3, then apply case 3 */
node case_2_1(node a, node b, node c, node d)
	requires a::rb1<0, bha, S1> * b::rb1<0, bha, S2> * c::rb1<0, bha, S3> * d::rb1<0, bha, S4> 
	ensures res::rb1<0, bha + 1, S5> & S5 = union(S1, S2, S3, S4, {0}, {0}, {0});

{
	node tmp;

	tmp = new node(0, 1, a, b);

	return  rotate_case_3_1(tmp, c, d);
}

/* RIGHT */
/* rotation case 3 */
node rotate_case_3r_1(node a, node b, node c)

	requires a::rb1<0, bha, S1> * b::rb1<0, bha, S2> * c::rb1<1, bha, S3>
	ensures res::rb1<0, bha + 1, S4> & S4 = union(S1, S2, S3, {0}, {0});

{
	node tmp;

	tmp = new node(0, 1, a, b);
	
	return new node(0, 0, tmp, c);
}

/* rotation to transform case 2 in case 3, then apply case 3 */
node case_2r_1(node a, node b, node c, node d)
	
	requires a::rb1<0, bha, S1> * b::rb1<0, bha, S2> * c::rb1<0, bha, S3> * d::rb1<0, bha, S4>
	ensures res::rb1<0, bha + 1, S5> & S5 = union(S1, S2, S3, S4, {0}, {0}, {0});

{
	node tmp;

	tmp = new node(0, 1, c, d);

	return rotate_case_3r_1(a, b, tmp);
}


/* function to check if a node is red */
bool is_red_1(node x)
	
	requires x::rb1<cl, bh, S>
	ensures x::rb1<cl, bh, S> & cl = 1 & res
		or x::rb1<cl, bh, S> & cl = 0 & !res;

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

	requires x::rb1<cl, bh, S>
	ensures x::rb1<cl, bh, S> & cl = 1 & !res
		or x::rb1<cl, bh, S> & cl = 0 & res;

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
node del_6_1(node a, node b, node c, int color)
	requires a::rb1<0, h, S1> * b::rb1<_, h, S2> * c::rb1<1, h, S3> & color = 0 or 
		 a::rb1<0, h, S1> * b::rb1<_, h, S2> * c::rb1<1, h, S3> & color = 1  
	ensures res::rb1<0, h + 2, S4> & S4 = union(S1, S2, S3, {0}, {0}) & color = 0 or 
		res::rb1<1, h + 1, S5> & S5 = union(S1, S2, S3, {0}, {0}) & color = 1;
 
{
	node tmp; 

	c.color = 0;
	tmp = new node(0, 0, a, b);

	return new node(0, color, tmp, c);
}

/* function for case 6 at delete (simple rotation) - when is right child */
node del_6r_1(node a, node b, node c, int color)

	requires a::rb1<1, ha, S1> * b::rb1<_, ha, S2> * c::rb1<0, ha, S3> & color = 0 or 
		 a::rb1<1, ha, S1> * b::rb1<_, ha, S2> * c::rb1<0, ha, S3> & color = 1 
	ensures res::rb1<0, ha + 2, S4> & S4 = union(S1, S2, S3, {0}, {0}) & color = 0 or 
		res::rb1<1, ha + 1, S4> & S4 = union(S1, S2, S3, {0}, {0}) & color = 1;

{
	node tmp;
	
	a.color = 0;
	tmp = new node(0, 0, b, c);

	return new node(0, color, a, tmp);	
}

/* function for case 5 (double rotation) */
node del_5_1(node a, node b, node c, node d, int color)

	requires a::rb1<0, h, S1> * b::rb1<0, h, S2> * c::rb1<0, h, S3> * d::rb1<0, h, S4> & color = 0 or 
		 a::rb1<0, h, S1> * b::rb1<0, h, S2> * c::rb1<0, h, S3> * d::rb1<0, h, S4> & color = 1 
	ensures res::rb1<0, h + 2, S5> & S5 = union(S1, S2, S3, S4, {0}, {0}, {0}) & color = 0 or 
		res::rb1<1, h + 1, S5> & S5 = union(S1, S2, S3, S4, {0}, {0}, {0}) & color = 1;

{
	node tmp;
	
	tmp = new node(0, 1, c, d);

	return del_6_1(a, b, tmp, color);
}


/* function for case 5(double rotation) - right child */
node del_5r_1(node a, node b, node c, node d, int color)
	requires a::rb1<0, h, S1> * b::rb1<0, h, S2> * c::rb1<0, h, S3> * d::rb1<0, h, S4> & color = 0 or 
		 a::rb1<0, h, S1> * b::rb1<0, h, S2> * c::rb1<0, h, S3> * d::rb1<0, h, S4> & color = 1 
	ensures res::rb1<0, h + 2, S5> & S5 = union(S1, S2, S3, S4, {0}, {0}, {0}) & color = 0 or 
		res::rb1<1, h + 1, S5> & S5 = union(S1, S2, S3, S4, {0}, {0}, {0}) & color = 1;
{
	node tmp;

	tmp = new node(0, 1, a, b);

	return del_6r_1(tmp, c, d, color);
}

/* function for case 4(just recolor) */
node del_4_1(node a, node b, node c)
	requires a::rb1<0, ha, S1> * b::rb1<0, ha, S2> * c::rb1<0, ha, S3> 
	ensures res::rb1<0, ha + 1, S4> & S4 = union(S1, S2, S3, {0}, {0});

{
	node tmp; 

	tmp = new node(0, 1, b, c);
	return new node(0, 0, a, tmp);
}


/* function for case 4 (just recolor) - right child */
node del_4r_1(node a, node b, node c)

	requires a::rb1<0, ha, S1> * b::rb1<0, ha, S2> * c::rb1<0, ha, S3> 
	ensures res::rb1<0, ha + 1, S4> & S4 = union(S1, S2, S3, {0}, {0});

{
	node tmp; 

	tmp = new node(0, 1, a, b);

	return new node(0, 0, tmp, c);
}


/* function for case 3 (just recolor) */
node del_3_1(node a, node b, node c)
	requires a::rb1<0, ha, S1> * b::rb1<0, ha, S2> * c::rb1<0, ha, S3> 
	ensures res::rb1<0, ha + 1, S4> & S4 = union(S1, S2, S3, {0}, {0});
{
	node tmp;

	tmp = new node(0, 1, b, c);
	
	return new node(0, 0, a, tmp);
}

/* function for case 3 (just recolor) - right child */
node del_3r_1(node a, node b, node c)

	requires a::rb1<0, ha, S1> * b::rb1<0, ha, S2> * c::rb1<0, ha, S3> 
	ensures res::rb1<0, ha + 1, S4> & S4 = union(S1, S2, S3, {0}, {0});

{
	node tmp;

	tmp = new node(0, 1, a, b);

	return new node(0, 0, tmp, c);
}


/* function for case 2 (simple rotation + applying one of the cases 4, 5, 6) */
node del_2_1(node a, node b, node c)
	requires a::rb1<0, h, S1> * b::rb1<0, h+1, S2> * c::rb1<0, h+1, S3> & b != null & c != null
	ensures res::rb1<0, h + 2, S4> & S4 = union(S1, S2, S3, {0}, {0});

{
	node tmp; 

	if (is_black_1(b.right))
	{
		if (is_black_1(b.left))
			tmp = del_4_1(a, b.left, b.right);
		else 
			tmp = del_5_1(a, b.left.left, b.left.right, b.right, 1);
	}
	else 
		{assume false; tmp = del_6_1(a, b.left, b.right, 1);}
	return new node(0, 0, tmp, c);
}

node del_2r_1(node a, node b, node c)

	requires a::rb1<0, h+1, S1> * b::rb1<0, h+1, S2> * c::rb1<0, h, S3> //& b != null //& a != null
	ensures res::rb1<0, h+2, S4> & S4 = union(S1, S2, S3, {0}, {0});

{
	node tmp, f; 

	if (is_black_1(b.left))
	{
		if (is_black_1(b.right))
			tmp = del_4r_1(b.left, b.right, c);
		else 
			tmp = del_5r_1(b.left, b.right.left, b.right.right, c, 1);
	}
	else 
		tmp = del_6r_1(b.left, b.right, c, 1);
	assert tmp'::rb1<_, h, S5> & S5 = union(S2, S3, {0});
	assert a'::rb1<0, h, S2>;
	assert a'::rb1<0, h+1, S1>;
	f = new node(0, 0, a, tmp);
	//assert f'::rb<_,_,_>;	
	return f;
}

int bh(node x) requires true ensures false;

/* function to delete the smalles element in a rb and then rebalance */
int remove_min_1(ref node x)

	requires x::rb1<cl, bh, S1> & x != null & 0 <= cl <= 1
	ensures x'::rb1<cl2, bh, S2> & S1 = union(S2, {res}) & cl = 1 & 0 <= cl2 <= 1
		or x'::rb1<0, bh2, S3> & S1 = union(S3, {res}) & bh-1 <= bh2 <= bh & cl = 0;

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
						x = del_2_1(x.left, x.right.left, x.right.right);
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
								x = del_3_1(x.left, x.right.left, x.right.right);
								return v1;
							}	
							else
							{
								x = del_4_1(x.left, x.right.left, x.right.right);
								return v1;
							}
						else
						{
							x = del_5_1(x.left, x.right.left.left, x.right.left.right, x.right.right, x.color);
							return v1;
						}
					}
					else
					{
						x = del_6_1(x.left, x.right.left, x.right.right, x.color);
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
	requires x::rb1<cl, bh, S1> & 0 <= cl <= 1
	ensures  x'::rb1<cl2, bh, S2> & S1 = union(S2, {a}) & cl = 1 & 0 <= cl2 <= 1 
	or x'::rb1<0, bh2, S2> & S1 = union(S2, {a}) & bh-1 <= bh2 <= h & cl = 0 
	or x'::rb1<cl, bh, S1>;

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
								x = del_2r_1(x.left.left, x.left.right, x.right);
						}
						else 
						{
							if (is_black_1(x.left.left))
								if (is_black_1(x.left.right))
									if (x.color == 0)
										x = del_3r_1(x.left.left, x.left.right, x.right);
									else
										x = del_4r_1(x.left.left, x.left.right, x.right);
								else 
									x = del_5r_1(x.left.left, x.left.right.left, x.left.right.right, x.right, x.color);
							else
								x = del_6r_1(x.left.left, x.left.right, x.right, x.color);
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
								x = del_2r_1(x.left.left, x.left.right, x.right);
						}
						else 	

						{
							if (is_black_1(x.left.left))
								if (is_black_1(x.left.right))
									if (x.color == 0)
										x = del_3r_1(x.left.left, x.left.right, x.right);
									else 
										x = del_4r_1(x.left.left, x.left.right, x.right);
								else 
									x = del_5r_1(x.left.left, x.left.right.left, x.left.right.right, x.right, x.color);
							else 
								x = del_6r_1(x.left.left, x.left.right, x.right, x.color);
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
								x = del_2_1(x.left, x.right.left, x.right.right);			
						}
						else 
						{
							if (is_black_1(x.right.right))
								if (is_black_1(x.right.left))
								{
									if (x.color == 0)
										x = del_3_1(x.left, x.right.left, x.right.right);
									else
										x = del_4_1(x.left, x.right.left, x.right.right);
								}
								else
									x = del_5_1(x.left, x.right.left.left, x.right.left.right, x.right.right, x.color);

							else 
								x = del_6_1(x.left, x.right.left, x.right.right, x.color);	
						}
				}
			}
		}
	}
}


node node_error() requires true ensures false; 

node insert_1(node x, int v)
	requires x::rb1<_, bh, S>
	ensures res::rb1< _, bh1, S1> & res != null & bh <= bh1 <= bh & S1 = union(S, {v});

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
							x = rotate_case_3_1(x.left.left, x.left.right, x.right);
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
								x = case_2_1(x.left.left, x.left.right.left, x.left.right.right, x.right);
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
							x = case_2r_1(x.left, x.right.left.left, x.right.left.right, x.right.right);
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
								x = rotate_case_3r_1(x.left, x.right.left, x.right.right);
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


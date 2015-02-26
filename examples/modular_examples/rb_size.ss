/* red black trees */

data node {
	int val;
	int color; /*  0 for black, 1 for red */
	node left;
	node right;
}

/* view for red-black trees */
/*
rb1<cl, bh, n> == 
	self = null & n = 0 & bh = 1 & cl = 0 or
	self::node<v, 1, l, r> * l::rb1<0, bhl, n1> * r::rb1<0, bhr, n2> & cl = 1 & bhl = bh & bhr = bh & n=n1+n2+1 or
	self::node<v, 0, l, r> * l::rb1<_, bhl, S1> * r::rb1<_, bhr, S2> & cl = 0 & bhl = bhr & bh = 1 + bhl & n=n1+n2+1
	inv bh >= 1 & 0 <= cl <= 1 & n >= 0;
*/
rb1<cl, bh, n> == self = null & n=0 & bh = 1 & cl = 0 
	or self::node<v, 1, l, r> * l::rb1<0, bhl, nl> * r::rb1<0, bhr, nr> & cl = 1 & n = 1 + nl + nr & bhl = bh & bhr = bh
	or self::node<v, 0, l, r> * l::rb1<_, bhl, nl> * r::rb1<_, bhr, nr> & cl = 0 & n = 1 + nl + nr & bhl = bhr & bh = 1 + bhl
	inv n >= 0 & bh >= 1 & 0 <= cl <= 1;

/* rotation case 3 */
node rotate_case_3_1(node a, node b, node c, int v1, int v2)

	requires a::rb1<1, bha, n1> * b::rb1<0, bha, n2> * c::rb1<0, bha, n3>
	ensures res::rb1<0, bha + 1, n> & n=n1+n2+n3+2;

{
	node tmp;

	tmp = new node(v2, 1, b, c);
	
	return new node(v1, 0, a, tmp);
}

/* rotation to transform case 2 in case 3, then apply case 3 */
node case_2_1(node a, node b, node c, node d, int v1, int v2, int v3)
	requires a::rb1<0, bha, n1> * b::rb1<0, bha, n2> * c::rb1<0, bha, n3> * d::rb1<0, bha, n4>
	ensures res::rb1<0, bha + 1, n> & n=n1+n2+n3+n4+3;

{
	node tmp;

	tmp = new node(v1, 1, a, b);

	return  rotate_case_3_1(tmp, c, d, v2, v3);
}

/* RIGHT */
/* rotation case 3 */
node rotate_case_3r_1(node a, node b, node c, int v1, int v2)

	requires a::rb1<0, bha, n1> * b::rb1<0, bha, n2> * c::rb1<1, bha, n3>
	ensures res::rb1<0, bha + 1, n> & n=n1+n2+n3+2;

{
	node tmp;

	tmp = new node(v1, 1, a, b);
	
	return new node(v2, 0, tmp, c);
}


/* rotation to transform case 2 in case 3, then apply case 3 */
node case_2r_1(node a, node b, node c, node d, int v1, int v2, int v3)
	
	requires a::rb1<0, bha, n1> * b::rb1<0, bha, n2> * c::rb1<0, bha, n3> * d::rb1<0, bha, n4>
	ensures res::rb1<0, bha + 1, n> & n=n1+n2+n3+n4+3;

{
	node tmp;

	tmp = new node(v3, 1, c, d);

	return rotate_case_3r_1(a, b, tmp, v1, v2);
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
node del_6_1(node a, node b, node c, int color, int v1, int v2)
/*
	requires case {
		color = 0 -> a::rb1<0, h, S1, n1> * b::rb1<_, h, S2, n2> * c::rb1<1, h, S3, n3> & forall (x : (x notin S1 | x <= v1)) & forall (y : (y notin S2 | y >= v1)) & forall (z : (z notin S2 | z <= v2)) & forall (w : (w notin S3 | w >= v2)) & v1<=v2; 
		color = 1 -> a::rb1<0, h, S1, n1> * b::rb1<_, h, S2, n2> * c::rb1<1, h, S3, n3> & forall (x : (x notin S1 | x <= v1)) & forall (y : (y notin S2 | y >= v1)) & forall (z : (z notin S2 | z <= v2)) & forall (w : (w notin S3 | w >= v2)) & v1<=v2;
	}  
	ensures case {
		color = 0 -> res::rb1<0, h + 2, S4, n4> & S4 = union(S1, S2, S3, {v1}, {v2}) & n4=n1+n2+n3+2;
		color = 1 -> res::rb1<1, h + 1, S5, n4> & S5 = union(S1, S2, S3, {v1}, {v2}) & n4=n1+n2+n3+2;
*/
	requires a::rb1<0, h, n1> * b::rb1<_, h, n2> * c::rb1<1, h, n3> & color = 0 or 
		 a::rb1<0, h, n1> * b::rb1<_, h, n2> * c::rb1<1, h, n3> & color = 1
	ensures res::rb1<0, h + 2, n> & n=n1+n2+n3+2 & color = 0 or 
		res::rb1<1, h + 1, n> & n=n1+n2+n3+2 & color = 1;
{
	node tmp; 

	c.color = 0;

	tmp = new node(v1, 0, a, b);

	return new node(v2, color, tmp, c);
}

/* function for case 6 at delete (simple rotation) - when is right child */
node del_6r_1(node a, node b, node c, int color, int v1, int v2)

	requires a::rb1<1, ha, n1> * b::rb1<_, ha, n2> * c::rb1<0, ha, n3> & color = 0 or 
		 a::rb1<1, ha, n1> * b::rb1<_, ha, n2> * c::rb1<0, ha, n3> & color = 1
	ensures res::rb1<0, ha + 2, n> & n=n1+n2+n3+2 & color = 0 or 
		res::rb1<1, ha + 1, n> & n=n1+n2+n3+2 & color = 1;

{
	node tmp;
	
	a.color = 0;
	
	tmp = new node(v2, 0, b, c);

	return new node(v1, color, a, tmp);	
}

/* function for case 5 (double rotation) */
node del_5_1(node a, node b, node c, node d, int color, int v1, int v2, int v3)

	requires a::rb1<0, h, n1> * b::rb1<0, h, n2> * c::rb1<0, h, n3> * d::rb1<0, h, n4> & color = 0 or 
		 a::rb1<0, h, n1> * b::rb1<0, h, n2> * c::rb1<0, h, n3> * d::rb1<0, h, n4> & color = 1
	ensures res::rb1<0, h + 2, n> & n=n1+n2+n3+n4+3 & color = 0 or 
		res::rb1<1, h + 1, n> & n=n1+n2+n3+n4+3 & color = 1;

{
	node tmp;
	
	tmp = new node(v3, 1, c, d);

	return del_6_1(a, b, tmp, color, v1, v2);
}


/* function for case 5(double rotation) - right child */
node del_5r_1(node a, node b, node c, node d, int color, int v1, int v2, int v3)
	requires a::rb1<0, h, n1> * b::rb1<0, h, n2> * c::rb1<0, h, n3> * d::rb1<0, h, n4> & color = 0 or 
		 a::rb1<0, h, n1> * b::rb1<0, h, n2> * c::rb1<0, h, n3> * d::rb1<0, h, n4> & color = 1 
	ensures res::rb1<0, h + 2, n> & n=n1+n2+n3+n4+3 & color = 0 or 
		res::rb1<1, h + 1, n> & n=n1+n2+n3+n4+3 & color = 1;
{
	node tmp;

	tmp = new node(v1, 1, a, b);

	return del_6r_1(tmp, c, d, color, v2, v3);
}

/* function for case 4(just recolor) */
node del_4_1(node a, node b, node c, int v1, int v2)
	requires a::rb1<0, ha, n1> * b::rb1<0, ha, n2> * c::rb1<0, ha, n3>  
	ensures res::rb1<0, ha + 1, n> & n=n1+n2+n3+2;

{
	node tmp; 

	tmp = new node(v2, 1, b, c);
	
	return new node(v1, 0, a, tmp);
}


/* function for case 4 (just recolor) - right child */
node del_4r_1(node a, node b, node c, int v1, int v2)

	requires a::rb1<0, ha, n1> * b::rb1<0, ha, n2> * c::rb1<0, ha, n3>  
	ensures res::rb1<0, ha + 1, n> & n=n1+n2+n3+2;

{
	node tmp; 

	tmp = new node(v1, 1, a, b);

	return new node(v2, 0, tmp, c);
}

/* function for case 3 (just recolor) */
node del_3_1(node a, node b, node c, int v1, int v2)
	requires a::rb1<0, ha, n1> * b::rb1<0, ha, n2> * c::rb1<0, ha, n3>   
	ensures res::rb1<0, ha + 1, n> & n=n1+n2+n3+2;
{
	node tmp;

	tmp = new node(v2, 1, b, c);
	
	return new node(v1, 0, a, tmp);
}

/* function for case 3 (just recolor) - right child */
node del_3r_1(node a, node b, node c, int v1, int v2)

	requires a::rb1<0, ha, n1> * b::rb1<0, ha, n2> * c::rb1<0, ha, n3>   
	ensures res::rb1<0, ha + 1, n> & n=n1+n2+n3+2;

{
	node tmp;

	tmp = new node(v1, 1, a, b);

	return new node(v2, 0, tmp, c);
}

/* function for case 2 (simple rotation + applying one of the cases 4, 5, 6) */
node del_2_1(node a, node b, node c, int v1, int v2)
	requires a::rb1<0, h, n1> * b::rb1<0, h+1, n2> * c::rb1<0, h+1, n3> & b != null & c != null
	ensures res::rb1<0, h + 2, n> & n=n1+n2+n3+2;

{
	node tmp; 

	if (is_black_1(b.right))
	{
		if (is_black_1(b.left)) {
			//assume false;
			tmp = del_4_1(a, b.left, b.right, v1, b.val);
		} else { 
			//assume false;
			tmp = del_5_1(a, b.left.left, b.left.right, b.right, 1, v1, b.left.val, b.val);
		}
	} else { 
		//assume false;
		tmp = del_6_1(a, b.left, b.right, 1, v1, b.val);
	}
	return new node(v2, 0, tmp, c);
}

node del_2r_1(node a, node b, node c, int v1, int v2)

	requires a::rb1<0, h+1, n1> * b::rb1<0, h+1, n2> * c::rb1<0, h, n3> & b != null //& a != null
	ensures res::rb1<0, h + 2, n> & n=n1+n2+n3+2;

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

	requires x::rb1<cl, bh, n1> & x != null & 0 <= cl <= 1
	ensures x'::rb1<cl2, bh, n2> & n2=n1-1 & cl = 1 & 0 <= cl2 <= 1 or
		x'::rb1<0, bh2, n3> & n3=n1-1 & bh-1 <= bh2 <= bh & cl = 0;

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
	requires x::rb1<cl, bh, n1> & 0 <= cl <= 1
	ensures  
	x'::rb1<cl2, bh, n2> & n1=n2+1 & cl = 1 & 0 <= cl2 <= 1 or
	x'::rb1<0, bh2, n2> & n1=n2+1 & bh-1 <= bh2 <= h & cl = 0 or
	x'::rb1<cl, bh, n1>;

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
	requires x::rb1<_, bh, n>
	ensures res::rb1< _, bh1, n1> & res != null & bh <= bh1 <= bh & n1=n+1;

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



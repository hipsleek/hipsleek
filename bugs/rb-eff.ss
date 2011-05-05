/* red black trees */

data node {
	int val;
	int color; /*  0 for black, 1 for red */
	node left;
	node right;
	int height;
}

/* view for red-black trees */
rb<n, cl, bh> == self = null & n=0 & bh = 1 & cl = 0 
	or self::node<v, 1, l, r> * l::rb<nl, 0, bhl> * r::rb<nr, 0, bhr> & cl = 1 & n = 1 + nl + nr & bhl = bh & bhr = bh
	or self::node<v, 0, l, r> * l::rb<nl, _, bhl> * r::rb<nr, _, bhr> & cl = 0 & n = 1 + nl + nr & bhl = bhr & bh = 1 + bhl
	inv n >= 0 & bh >= 1 & 0 <= cl <= 1;


/* rotation case 3 */

node rotate_case_3(node a, node b, node c)

	requires a::rb<na, 1, bha> * b::rb<nb, 0, bha> * c::rb<nc, 0, bha> 
	ensures res::rb<na + nb + nc + 2, 0, bha + 1>;

{
	node tmp;

	tmp = new node(0, 1, b, c);
	
	return new node(0, 0, a, tmp);
}


/* rotation to transform case 2 in case 3, then apply case 3 */
node case_2(node a, node b, node c, node d)

	requires a::rb<na, 0, bha> * b::rb<nb, 0, bha> * c::rb<nc, 0, bha> * d::rb<nd, 0, bha> 
	ensures res::rb<na + nb + nc + nd + 3, 0, bha + 1>;

{
	node tmp;

	tmp = new node(0, 1, a, b);

	return  rotate_case_3(tmp, c, d);
}

/* RIGHT */
/* rotation case 3 */
node rotate_case_3r(node a, node b, node c)

	requires a::rb<na, 0, bha> * b::rb<nb, 0, bha> * c::rb<nc, 1, bha>
	ensures res::rb<na + nb + nc + 2, 0, bha + 1>;

{
	node tmp;

	tmp = new node(0, 1, a, b);
	
	return new node(0, 0, tmp, c);
}


/* rotation to transform case 2 in case 3, then apply case 3 */
node case_2r(node a, node b, node c, node d)
	
	requires a::rb<na, 0, bha> * b::rb<nb, 0, bha> * c::rb<nc, 0, bha> * d::rb<nd, 0, bha>
	ensures res::rb<na + nb + nc + nd + 3, 0, bha + 1>;

{
	node tmp;

	tmp = new node(0, 1, c, d);

	return rotate_case_3r(a, b, tmp);
}


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


/* function for case 6 delete (simple rotation) */
node del_6(node a, node b, node c, int color)

	requires a::rb<na , 0, h> * b::rb<nb, _, h> * c::rb<nc, 1, h> & color = 0 or 
		 a::rb<na , 0, h> * b::rb<nb, _, h> * c::rb<nc, 1, h> & color = 1  
	ensures res::rb<na + nb + nc + 2, 0, h + 2> & color = 0 or 
		res::rb<na + nb + nc + 2, 1, h + 1> & color = 1;
 
{
	node tmp; 

	c.color = 0;
	tmp = new node(0, 0, a, b);

	return new node(0, color, tmp, c);
}

/* function for case 6 at delete (simple rotation) - when is right child */
node del_6r(node a, node b, node c, int color)

	requires a::rb<na , 1, ha> * b::rb<nb, _, ha> * c::rb<nc, 0, ha> & color = 0 or 
		 a::rb<na , 1, ha> * b::rb<nb, _, ha> * c::rb<nc, 0, ha> & color = 1 
	ensures res::rb<na + nb + nc + 2, 0, ha + 2> & color = 0 or 
		res::rb<na + nb + nc + 2, 1, ha + 1> & color = 1;

{
	node tmp;
	
	a.color = 0;
	tmp = new node(0, 0, b, c);

	return new node(0, color, a, tmp);	
}

/* function for case 5 (double rotation) */
node del_5(node a, node b, node c, node d, int color)

	requires a::rb<na , 0, h> * b::rb<nb, 0, h> * c::rb<nc, 0, h> * d::rb<nd, 0, h> & color = 0 or 
		 a::rb<na , 0, h> * b::rb<nb, 0, h> * c::rb<nc, 0, h> * d::rb<nd, 0, h> & color = 1 
	ensures res::rb<na + nb + nc + nd + 3, 0, h + 2> & color = 0 or 
		res::rb<na + nb + nc + nd + 3, 1, h + 1> & color = 1;

{
	node tmp;
	
	tmp = new node(0, 1, c, d);

	return del_6(a, b, tmp, color);
}

/* function for case 5(double rotation) - right child */
node del_5r(node a, node b, node c, node d, int color)
	requires a::rb<na , 0, h> * b::rb<nb, 0, h> * c::rb<nc, 0, h> * d::rb<nd, 0, h> & color = 0 or 
		 a::rb<na , 0, h> * b::rb<nb, 0, h> * c::rb<nc, 0, h> * d::rb<nd, 0, h> & color = 1 
	ensures res::rb<na + nb + nc + nd + 3, 0, h + 2> & color = 0 or 
		res::rb<na + nb + nc + nd + 3, 1, h + 1> & color = 1;
{
	node tmp;

	tmp = new node(0, 1, a, b);
	return del_6r(tmp, c, d, color);
}

/* function for case 4(just recolor) */
node del_4(node a, node b, node c)

	requires a::rb<na, 0, ha> * b::rb<nb, 0, ha> * c::rb<nc, 0, ha> 
	ensures res::rb<na + nb + nc + 2, 0, ha + 1>;

{
	node tmp1,tmp2; 
	tmp1 = new node(0, 1, b, c);
  tmp2 = new node(0, 0, a, tmp1);
	return tmp2;
}

/* function for case 4 (just recolor) - right child */
node del_4r(node a, node b, node c)

	requires a::rb<na, 0, ha> * b::rb<nb, 0, ha> * c::rb<nc, 0, ha> 
	ensures res::rb<na + nb + nc + 2, 0, ha + 1>;

{
	node tmp; 

	tmp = new node(0, 1, a, b);

	return new node(0, 0, tmp, c);
}

/* function for case 3 (just recolor) */
node del_3(node a, node b, node c)

	requires a::rb<na, 0, ha> * b::rb<nb, 0, ha> * c::rb<nc, 0, ha> 
	ensures res::rb<na + nb + nc + 2, 0, ha + 1>;


{
	node tmp;

	tmp = new node(0, 1, b, c);
	
	return new node(0, 0, a, tmp);
}

/* function for case 3 (just recolor) - right child */
node del_3r(node a, node b, node c)

	requires a::rb<na, 0, ha> * b::rb<nb, 0, ha> * c::rb<nc, 0, ha> 
	ensures res::rb<na + nb + nc + 2, 0, ha + 1>;

{
	node tmp;

	tmp = new node(0, 1, a, b);

	return new node(0, 0, tmp, c);
}

/* function for case 2 (simple rotation + applying one of the cases 4, 5, 6) */
node del_2(node a, node b, node c)

	requires a::rb<na, 0, h> * b::rb<nb, 0, h+1> * c::rb<nc, 0, h+1> & b != null & c != null
	ensures res::rb<na+nb+nc+2, 0, h + 2>;

{
	node tmp; 

	if (is_black(b.right))
	{
		if (is_black(b.left))
			tmp = del_4(a, b.left, b.right);
		else 
			tmp = del_5(a, b.left.left, b.left.right, b.right, 1);
	}
	else 
		tmp = del_6(a, b.left, b.right, 1);
	return new node(0, 0, tmp, c);
}


/************** it can assert that a'::rb<na, 0, h> & a'::rb<na, 0, h+1> and even that a'::rb<na + 5, 0, h> or a'::rb<nb, 0, h> */

/* function for case 2 (simple rotation + applying one of the cases 4, 5, 6) - right child*/
node del_2r(node a, node b, node c)

	requires a::rb<na, 0, h+1> * b::rb<nb, 0, h+1> * c::rb<nc, 0, h> & b != null //& a != null
	ensures res::rb<na+nb+nc+2, 0, h+2>;

{
	node tmp, f; 

	if (is_black(b.left))
	{
		if (is_black(b.right))
			tmp = del_4r(b.left, b.right, c);
		else 
			tmp = del_5r(b.left, b.right.left, b.right.right, c, 1);
	}
	else 
		tmp = del_6r(b.left, b.right, c, 1);
	assert tmp'::rb<nb+nc+1, _, ha> & h=ha;
	assert a'::rb<n_1, 0, hb> & hb=h & n_1=nb;
	assert a'::rb<n_2, 0, hc> & hc=h+1 & n_2=na;
	f = new node(0, 0, a, tmp);
	//assert f'::rb<_,_,_>;	
	return f;
}


/* not working, waiting for all the others to work to check the pbs*/ 
/* primitive for the black height */
//int bh(node x) requires true ensures false;

/*
-- below loses too much information
int bh(node x)
  requires x::rb<n,cl,bh>
  ensures x::rb<n,cl,bh> & res=bh;
*/
/*
int bh(node x) 
  requires x::rb<n,cl,h>@I
  ensures res=h;
*/
int bh(node x) 
 case {
   x=null -> res=1;
   x!=null -> requires x::node<a,b,c,d>
               ensures res=d;
 }
 {
   if (x==null) return 1;
    else return x.height;
 }

/* function to delete the smalles element in a rb and then rebalance */
int remove_min(ref node x)

/*
	requires x::rb<n, cl, bh> & x != null & 0 <= cl <= 1
	ensures x'::rb<n-1, cl2, bh> & cl = 1 & 0 <= cl2 <= 1
		or x'::rb<n-1, 0, bh2> & bh-1 <= bh2 <= bh & cl = 0;
*/ 

	requires x::rb<n, cl, bh> & x != null 
    case { cl=1 -> ensures x'::rb<n-1, cl2, bh>;
           cl=0 -> ensures x'::rb<n-1, 0, bh2> & bh-1 <= bh2 <= bh;
           (cl<0 | cl>1) -> ensures false;
    }
{
	int v1;

	if (x.left == null)
	{
      assume false;
		int tmp = x.val;

		if (is_red(x.right))
			x.right.color = 0; 
		x = x.right;
	
		return tmp;
	}
	else 
	{	v1 = remove_min(x.left);
		//rebalance 
      dprint;
      int lh = bh(x.left);
      assume false;
      int rh = bh(x.right);

		if (lh < rh)
		{
          assume false;
			if (is_black(x.left))
			{	if (is_red(x.right))
				{
					if (x.right.left != null)
                                        {
						x = del_2(x.left, x.right.left, x.right.right);
                                                return v1;
                                        }
					else
						return v1;
				}
				else 
				{
					if (is_black(x.right.right))
					{
						if (is_black(x.right.left))
							if (x.color == 0)
							{
								x = del_3(x.left, x.right.left, x.right.right);
								return v1;
							}	
							else
							{
								x = del_4(x.left, x.right.left, x.right.right);
								return v1;
							}
						else
						{
							x = del_5(x.left, x.right.left.left, x.right.left.right, x.right.right, x.color);
							return v1;
						}
					}
					else
					{
						x = del_6(x.left, x.right.left, x.right.right, x.color);
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
void del(ref node  x, int a)

	requires x::rb<n, cl, bh> & 0 <= cl <= 1
	ensures  x'::rb<n-1, cl2, bh> & cl = 1 & 0 <= cl2 <= 1 
		 or x'::rb<n-1, 0, bh2> & bh-1 <= bh2 <= h & cl = 0 
		 or x'::rb<n, cl, bh>;
/*
  requires x::rb<n, cl, bh> 
    case { cl=1 -> ensures x'::rb<n-1, cl2, bh> 
                   or x'::rb<n, cl, bh>;
         cl=0 -> ensures x'::rb<n-1, 0, bh2> & bh-1 <= bh2 <= h
                   or x'::rb<n, cl, bh>;
        (cl<0 | cl>1) -> ensures false;
    }
*/
{
	int v;

    assert false;if (x!=null)
      {  assert false;
		if (x.val == a) // delete x
         { 
			if (x.right == null)
			{ 
				if (is_red(x.left))
                  x.left.color = 0;
				x = x.left;

			}
			else 
			{
				v = remove_min(x.right);
				if (bh(x.right) < bh(x.left))
				{
					if (is_black(x.right))
					{
						if (is_red(x.left))	
						{
							if (x.left.right != null)
								x = del_2r(x.left.left, x.left.right, x.right);
						}
						else 
						{
							if (is_black(x.left.left))
								if (is_black(x.left.right))
									if (x.color == 0)
										x = del_3r(x.left.left, x.left.right, x.right);
									else
										x = del_4r(x.left.left, x.left.right, x.right);
								else 
									x = del_5r(x.left.left, x.left.right.left, x.left.right.right, x.right, x.color);
							else
								x = del_6r(x.left.left, x.left.right, x.right, x.color);
						}
								
					}
				}		
			}
		}
		else 
		{
			if (x.val < a) //go right 
			{
				del(x.right, a);

				// rebalance
				if (bh(x.right) < bh(x.left))
				{
					if (is_black(x.right))
						if (is_red(x.left))
						{
							if (x.left.right != null)
								x = del_2r(x.left.left, x.left.right, x.right);
						}
						else 	

						{
							if (is_black(x.left.left))
								if (is_black(x.left.right))
									if (x.color == 0)
										x = del_3r(x.left.left, x.left.right, x.right);
									else 
										x = del_4r(x.left.left, x.left.right, x.right);
								else 
									x = del_5r(x.left.left, x.left.right.left, x.left.right.right, x.right, x.color);
							else 
								x = del_6r(x.left.left, x.left.right, x.right, x.color);
						}
				}
			}
			else   // go left 
			{
				del(x.left, a);

				// rebalance 
				if (bh(x.left) < bh(x.right))
				{
					if (is_black(x.left))
						if (is_red(x.right))
						{
							if (x.right.left != null)
								x = del_2(x.left, x.right.left, x.right.right);			
						}
						else 
						{
							if (is_black(x.right.right))
								if (is_black(x.right.left))
								{
									if (x.color == 0)
										x = del_3(x.left, x.right.left, x.right.right);
									else
										x = del_4(x.left, x.right.left, x.right.right);
								}
								else
									x = del_5(x.left, x.right.left.left, x.right.left.right, x.right.right, x.color);

							else 
								x = del_6(x.left, x.right.left, x.right.right, x.color);	
						}
				}
			}
		}
	}
}

/*
node test_insert(node x, int v)

	requires x::rb<xn, _, _>
	ensures x::rb<_, _, _> & res != null;

{
	node tmp;
	//assert a'::rb<na, 0, h>;

	if (x == null)
	{
		
		tmp =  new node(v, 1, null, null);	
		return tmp;
	}
	else 
		return x;

}
*/

node node_error() requires true ensures false; 

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
							x = rotate_case_3(x.left.left, x.left.right, x.right);
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
								x = case_2(x.left.left, x.left.right.left, x.left.right.right, x.right);
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
							x = case_2r(x.left, x.right.left.left, x.right.left.right, x.right.right);
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
								x = rotate_case_3r(x.left, x.right.left, x.right.right);
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


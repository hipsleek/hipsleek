/* red black trees */

data node {
	int val;
	int color; /*  0 for black, 1 for red */
	node left;
	node right;
}

/* view for red-black trees */
rb1<cl> == self = null & cl = 0
	or self::node<v, 1, l, r> * l::rb1<0> * r::rb1<0> & cl = 1
	or self::node<v, 0, l, r> * l::rb1<_> * r::rb1<_> & cl = 0
	inv 0 <= cl <= 1;

node rotate_case_3_1(node a, node b, node c)
  requires a::rb1<1> * b::rb1<0> * c::rb1<0> & a!=null
  ensures res::rb1<cl> & cl=0 & res!=null;

node rotate_case_3(node a, node b, node c)
  infer @post []
  requires a::rb1<1> * b::rb1<0> * c::rb1<0>
  ensures res::rb1<cl>;
{
	node tmp;

	tmp = new node(0, 1, b, c);

	return new node(0, 0, a, tmp);
}


/* rotation to transform case 2 in case 3, then apply case 3 */
node case_2_1(node a, node b, node c, node d)
  requires a::rb1<0> * b::rb1<0> * c::rb1<0> * d::rb1<0>
  ensures res::rb1<cl> & cl=0 & res!=null;

node case_2(node a, node b, node c, node d)
  infer @post []
  requires a::rb1<0> * b::rb1<0> * c::rb1<0> * d::rb1<0>
  ensures res::rb1<cl>;
{
	node tmp;

	tmp = new node(0, 1, a, b);

	return  rotate_case_3_1(tmp, c, d);
}

/* RIGHT */
/* rotation case 3 */
node rotate_case_3r_1(node a, node b, node c)
  requires a::rb1<0> * b::rb1<0> * c::rb1<1> & c!=null
  ensures res::rb1<cl> & cl=0 & res!=null;

node rotate_case_3r(node a, node b, node c)
  infer @post []
  requires a::rb1<0> * b::rb1<0> * c::rb1<1>
  ensures res::rb1<cl>;
{
	node tmp;

	tmp = new node(0, 1, a, b);

	return new node(0, 0, tmp, c);
}

/* rotation to transform case 2 in case 3, then apply case 3 */
node case_2r_1(node a, node b, node c, node d)
  requires a::rb1<0> * b::rb1<0> * c::rb1<0> * d::rb1<0>
  ensures res::rb1< cl> & cl=0 & res!=null;

node case_2r(node a, node b, node c, node d)
  infer @post []
  requires a::rb1<0> * b::rb1<0> * c::rb1<0> * d::rb1<0>
  ensures res::rb1< cl>;
{
	node tmp;

	tmp = new node(0, 1, c, d);

	return rotate_case_3r_1(a, b, tmp);
}

/* function to check if a node is red */
bool is_red_1(node x)
  requires x::rb1<cl>
 case {
  x=null -> ensures !res;
  x!=null ->  ensures x::rb1<cl>& cl = 1 & res or x::rb1<cl> & cl = 0 & !res;
}

relation IR1(int a, bool b).
relation IR2(int a, bool b).
bool is_red(node x)
  infer[IR1,IR2]
  requires x::rb1<cl>
 case {
  cl=0 -> ensures x::rb1<cl> & IR1(cl,res);
  cl!=0 -> ensures x::rb1<cl> & IR2(cl,res);
}
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
  requires x::rb1<cl>
 case {
  x=null -> ensures x=null & res;
  x!=null -> ensures x::rb1<1> & !res  or x::rb1<0> & res;
}

relation IB1(int a, bool b).
relation IB2(int a, bool b).
bool is_black(node x)
  infer[IB1,IB2,x]
  requires x::rb1<cl>
   case {
  cl=1 -> ensures x::rb1<cl> & IB1(cl,res);
  cl!=1 -> ensures x::rb1<cl> & IB2(cl,res);
}
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
  requires a::rb1<0> * b::rb1< _> * c::rb1<1> & color = 0 & c!=null or
  a::rb1<0> * b::rb1<_> * c::rb1<1> & color = 1 & c!=null
  ensures res::rb1<cl> & 0=cl & color=0 & res!=null or
  res::rb1<cl> & 1=cl & color=1 & res!=null;

node del_6(node a, node b, node c, int color)
  infer @post []
  requires a::rb1<0> * b::rb1< _> * c::rb1<1> & color = 0 or 
  a::rb1<0> * b::rb1<_> * c::rb1<1> & color = 1
  ensures res::rb1<cl> & color = 0 or  res::rb1<cl> & color = 1;
{
	node tmp;

	c.color = 0;
	tmp = new node(0, 0, a, b);

	return new node(0, color, tmp, c);
}

/* function for case 6 at delete (simple rotation) - when is right child */
node del_6r_1(node a, node b, node c, int color)
  requires a::rb1<1> * b::rb1<_> * c::rb1<0> & color = 0 & null!=a or //null!=a
  a::rb1<1> * b::rb1<_> * c::rb1<0> & color = 1 & null!=a
 case {
  color=0 -> ensures res::rb1<cl> & 0=cl;
  color!=0 -> ensures res::rb1<cl> & 1=cl;
}

node del_6r(node a, node b, node c, int color)
  infer @post []
  requires a::rb1<1> * b::rb1<_> * c::rb1<0> & color = 0 or //null!=a
  a::rb1<1> * b::rb1<_> * c::rb1<0> & color = 1
  ensures res::rb1<cl> & color = 0 or res::rb1<cl> & color = 1;
{
	node tmp;

	a.color = 0;
	tmp = new node(0, 0, b, c);

	return new node(0, color, a, tmp);
}

/* function for case 5 (double rotation) */
node del_5_1(node a, node b, node c, node d, int color)
  requires a::rb1<0> * b::rb1<0> * c::rb1<0> * d::rb1<0> & color = 0 or
  a::rb1<0> * b::rb1<0> * c::rb1<0> * d::rb1<0> & color = 1
  ensures res::rb1<cl> & color = 0 & cl=0 or res::rb1<cl> & cl=1 & color = 1 & res!=null;

node del_5(node a, node b, node c, node d, int color)
  infer @post []
  requires a::rb1<0> * b::rb1<0> * c::rb1<0> * d::rb1<0> & color = 0 or
  a::rb1<0> * b::rb1<0> * c::rb1<0> * d::rb1<0> & color = 1
  ensures res::rb1<cl> & color = 0 or res::rb1<cl> & color = 1;
{
	node tmp;

	tmp = new node(0, 1, c, d);

	return del_6_1(a, b, tmp, color);
}

/* function for case 5(double rotation) - right child */
node del_5r_1(node a, node b, node c, node d, int color)
  requires a::rb1<0> * b::rb1<0> * c::rb1<0> * d::rb1<0> & color = 0 or
  a::rb1<0> * b::rb1<0> * c::rb1<0> * d::rb1<0> & color = 1
  ensures res::rb1<cl> & cl=0 & color = 0 or res::rb1<cl> & cl=1 & color = 1 & res!=null;

node del_5r(node a, node b, node c, node d, int color)
  infer @post []
  requires a::rb1<0> * b::rb1<0> * c::rb1<0> * d::rb1<0> & color = 0 or
  a::rb1<0> * b::rb1<0> * c::rb1<0> * d::rb1<0> & color = 1
  ensures res::rb1<cl> & color = 0 or res::rb1<cl> & color = 1;
{
	node tmp;

	tmp = new node(0, 1, a, b);
	return del_6r_1(tmp, c, d, color);
}

/* function for case 4(just recolor) */
node del_4_1(node a, node b, node c)
  requires a::rb1<0> * b::rb1<0> * c::rb1<0>
  ensures res::rb1<cl> & cl=0 & res!=null;

node del_4(node a, node b, node c)
  infer @post []
  requires a::rb1<0> * b::rb1<0> * c::rb1<0>
  ensures res::rb1<cl>; 
{
	node tmp1,tmp2;
	tmp1 = new node(0, 1, b, c);
    tmp2 = new node(0, 0, a, tmp1);
	return tmp2;
}

/* function for case 4 (just recolor) - right child */
node del_4r_1(node a, node b, node c)
  requires a::rb1<0> * b::rb1<0> * c::rb1<0>
  ensures res::rb1<cl> & cl=0 & res!=null;

node del_4r(node a, node b, node c)
  infer @post []
  requires a::rb1<0> * b::rb1<0> * c::rb1<0>
  ensures res::rb1<cl>;
{
	node tmp;

	tmp = new node(0, 1, a, b);

	return new node(0, 0, tmp, c);
}

/* function for case 3 (just recolor) */
node del_3_1(node a, node b, node c)
  requires a::rb1<0> * b::rb1<0> * c::rb1<0>
  ensures res::rb1<cl> & cl=0 & res!=null;

node del_3(node a, node b, node c)
  infer @post []
  requires a::rb1<0> * b::rb1<0> * c::rb1<0>
  ensures res::rb1<cl>;
{
	node tmp;

	tmp = new node(0, 1, b, c);

	return new node(0, 0, a, tmp);
}

/* function for case 3 (just recolor) - right child */
node del_3r_1(node a, node b, node c)
  requires a::rb1<0> * b::rb1<0> * c::rb1<0>
  ensures res::rb1<cl> & cl=0 & res!=null;

node del_3r(node a, node b, node c)
  infer @post []
  requires a::rb1<0> * b::rb1<0> * c::rb1<0>
  ensures res::rb1<cl>;
{
	node tmp;

	tmp = new node(0, 1, a, b);

	return new node(0, 0, tmp, c);
}

/* function for case 2 (simple rotation + applying one of the cases 4, 5, 6) */
node del_2_1(node a, node b, node c)
  requires a::rb1<0> * b::rb1<0> * c::rb1<0> & b != null
  ensures res::rb1<cl> & cl=0 & res!=null;

node del_2(node a, node b, node c)
  infer[res,b]
  requires a::rb1<0> * b::rb1<0> * c::rb1<0> 
  ensures res::rb1<cl>;
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
		tmp = del_6_1(a, b.left, b.right, 1);
	return new node(0, 0, tmp, c);
}


/************** it can assert that a'::rb<na, 0, h> & a'::rb<na, 0, h+1> and even that a'::rb<na + 5, 0, h> or a'::rb<nb, 0, h> */
node del_2r_1(node a, node b, node c)
	requires a::rb1<0> * b::rb1<0> * c::rb1< 0> & b != null
	ensures res::rb1<0> & res!=null;

/* function for case 2 (simple rotation + applying one of the cases 4, 5, 6) - right child*/
node del_2r(node a, node b, node c)
  infer[a,b,res]
  requires a::rb1<0> * b::rb1<0> * c::rb1<0>
  ensures res::rb1<cl>;
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
	f = new node(0, 0, a, tmp);
	return f;
}


/* not working, waiting for all the others to work to check the pbs*/
/* primitive for the black height */
int bh(node x) requires true ensures false;

/* function to delete the smalles element in a rb and then rebalance */
int remove_min_1(ref node x)
  requires x::rb1<cl> & x != null
  ensures x'::rb1<cl2> & cl = 1 & 0 <= cl2 <= 1 or x'::rb1<0> & cl = 0;

relation RMVM1(int a, int b).
relation RMVM2(int a, int b).
int remove_min(ref node x)
  infer[x,RMVM1,RMVM2]
  requires x::rb1<cl> 
  ensures x'::rb1<cl2> & cl = 1 & RMVM1(cl2,cl) or x'::rb1<cl3> &  RMVM2(cl3,cl);
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
      v1 = remove_min(x.left);

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
relation DEL1(int a, int b).
relation DEL2(int a, int b).
void del(ref node  x, int a)
  infer[x,DEL1,DEL2]
	requires x::rb1<cl>
	ensures  x'::rb1<cl2> & cl = 1 & 0 <= cl2 <= 1 & DEL2(cl2,cl)
		 or x'::rb1<cl3> & cl = 0 & DEL1(cl3,cl)
		 or x'::rb1<cl>;
{
	int v;

  if (x!=null)
    {  
      if (x.val == a) 
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
          if (x.val < a) 
			{
              del(x.right, a);

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
          else  
			{
              del(x.left, a);
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
relation INS(node a).
node insert(node x, int v)
  infer[INS]
  requires x::rb1<_>
  ensures res::rb1<_> & INS(res);
{
	node tmp, tmp_null = null;

	if (x == null)

      return new node(v, 1, tmp_null, tmp_null);
	else
	{
      if (v <= x.val)
		{
          tmp = x.left;
          x.left = insert(tmp, v);
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
          { 
			tmp = x.right;
			x.right = insert(tmp, v);

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


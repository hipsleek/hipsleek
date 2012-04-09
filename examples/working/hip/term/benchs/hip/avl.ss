data node {
	int val;
	int height;
	node left;
	node right;
}

data myint {
  int val;
}

/* view for avl trees */
avl<n, h> == 
	self = null & n = 0 & h = 0 or 
	self::node<_, h, p, q> * p::avl<n1, h1> * q::avl<n2, h2>
		& n = 1+n1+n2
		& h2<=h1+1 & h1<=h2+1 & h = max(h1, h2) + 1 
	inv n >= 0 & h >= 0;

/* function to return the height of an avl tree */
int height(node x)

	requires x::avl<m, n> & Term
	ensures x::avl<m, n> & res = n;	

{
	if (x == null)
		return 0;
	else
		return x.height;
}

/* function to rotate left */
node rotate_left(node l, node rl, node rr)

	requires l::avl<lm, ln> * rl::avl<rlm, ln> * rr::avl<rrm, ln+1> & Term
	ensures res::avl<2+lm+rlm+rrm, 2+ln>;	

{
	node tmp;
	int v = 10;
	int	h = height(l) + 1;

	tmp = new node(v, h, l, rl);	
	h = h + 1;
	return new node(v, h, tmp, rr);
}

/* function to rotate right */
node rotate_right(node ll, node lr, node r)

	requires ll::avl<llm, lln> * lr::avl<lrm, lln - 1> * r::avl<rm, lln - 1> & Term 
	ensures res::avl<2 + llm + lrm + rm, 1 + lln>; 

{
	node tmp; 
	int v = 10;
	int h = height(r) + 1;
	
	tmp = new node(v, h, lr, r);
	h = h + 1;
	return new node(v, h, ll, tmp);
}

int get_max(int a , int b)
	
	requires Term 
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
	         & -1 <= bn - cn <= 1 & Term
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
	         & an = max(bn, cn) & -1 <= cn - bn <= 1 & Term
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

	requires x::avl<mx, nx> * y::avl<my, nx> & x != null & Term
	ensures res::avl<1 + mx + my, 1 + nx>;

{
	int v = 0;
	int tmp;

	tmp = x.height;
	tmp = tmp + 1;
	return new node(v, tmp, x, y);	
}

void build_avl2(node x, node y, node z)
	
	requires y::avl<my, ny> * z::avl<mz, ny> * x::node<_, _, _, _> & y != null & Term
	ensures  x::avl<1 + my + mz, 1 + ny>;

{
	int tmp;

	x.left = y;
	x.right = z;
	x.height = y.height  + 1;
}

node node_error() requires Term ensures false;

/* function to insert a node in an avl tree (using the rotate functions) */
node insert(node x, int a)

	requires x::avl<m, n> & Term[m]
//	ensures res::avl<m + 1, n1>;
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
					//dprint;
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

/* function to insert in an avl tree (inline version) */
node insert_inline(node x, int a)

	requires x::avl<m, n> & Term[m] 
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

/*
/* function to delete the smallest element in an avl tree */
int remove_min(ref node x)
	requires x::avl<m,n> & x != null & Term[m]
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
*/
/*
node remove_min_add(node x)
  requires x::avl<m, n> & x != null & Term[m]
  ensures res::avl<m, n>;

node remove_min(node x)
  requires x::avl<m, n> & x != null
  ensures res::avl<m - 1, n1> & n-1 <= n1 <= n;
{
  if (x.left == null) {
    node t = x.right;
    return t;
  } else {
    if (height(x.left) < height(x.right)) {
      // assert x.right != null;
      x.left = remove_min_add(x.left);
      x.right = remove_min(x.right);
      x.height = get_max(height(x.left), height(x.right)) + 1;
      return x;
    } else {
      x.left = remove_min(x.left);
      x.height = get_max(height(x.left), height(x.right)) + 1;
      return x;
    }
  }
}
*/

node remove_min_add(node x, ref myint a)
  requires x::avl<m,n> * a::myint<vv> & x != null & Term[m]
  ensures res::avl<m,n> * a'::myint<r> & r <= vv;

node remove_min(node x, ref myint a)
    requires x::avl<m, n> * a::myint<_> & x != null
    ensures res::avl<m - 1, nn> * a'::myint<r> & n-1 <= nn <= n;
{
  myint ret = new myint(0),tmp = new myint(0);
  //int hl, hr;
  if (x.left == null) {
    a.val = x.val;
    node t = x.right;
    return t;
  } else {
    if (height(x.left) < height(x.right)) {
      // assert x.right != null;
      ret.val = x.val;
      x.left = remove_min_add(x.left, ret);
      a.val = ret.val;
      x.right = remove_min(x.right, tmp);
      x.val = tmp.val;
      x.height = get_max(height(x.left), height(x.right)) + 1;
      return x;
    } else {
      x.left = remove_min(x.left, a);
      x.height = get_max(height(x.left), height(x.right)) + 1;
      return x;
    }
  }
}


/*
/* function to delete a node in a an avl tree */
void delete(ref node x, int a)

	requires x::avl<m, n> & Term[m] 
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

node merge(node t1, node t2)
/*requires t2::avl<s2,h2>
case {
      t1=null -> ensures res::avl<s2,h2>;
      t1!=null -> requires t1::avl<s1,h1>  ensures res::avl<s1+s2,_>;
}*/

case {
      t1=null -> requires t2::avl<s2,h2> & Term ensures res::avl<s2,h2>;
      t1!=null -> requires t1::avl<s1,h1> * t2::avl<s2,h2> & Term[s1] ensures res::avl<s1+s2,_>;
}


//requires t2::avl<s2,h2> & t1=null
//ensures res::avl<s2,h2>;
//requires t1::avl<s1,h1> * t2::avl<s2,h2> & t1!=null 
//ensures res::avl<s2,h2>;

{
 	if (t1 == null) return t2;
  else {
	  node tmp = insert(t2, t1.val);
	  node tmp1 = merge (t1.left, tmp);
	  return merge(t1.right, tmp1);
		//node tmp1 = merge (tmp, t1.left);
	  //return merge(tmp1, t1.right);
	}
}

//Loop version of merge
node merge2(node t1, node t2)
case {
	t1=null -> requires t2::avl<s2,h2> & Term ensures res::avl<s2,h2>;
  t1!=null -> requires t1::avl<s1,h1> * t2::avl<s2,h2> & Loop ensures false;
}
{
 	if (t1 == null) return t2;
  else {
	  node tmp = insert(t2, t1.val);
		node tmp1 = merge2(tmp, t1.left);
	  return merge2(tmp1, t1.right);
	}
}

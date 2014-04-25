/* avl trees */
/*not working/provable code */
/* representation of a node in an avl tree */
data node {
	int val;
	int height;
	node left;
	node right;
}

/* view for avl trees */
/**** for omega nd mona ****/
avl2<n, S> == self = null & S = {} & n = 0 
  or (exists n3,tmp: self::node<v, n, p, q> * p::avl2<n1, S1> * q::avl2<n2, S2> & S = union(S1, S2, {v}) & 
      n3 =  max(n1-n2, n2-n1) & n3 <= 1 & tmp = max(n1, n2) & n = tmp + 1) 
	inv n >= 0;

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
	or self::node<v, n, p, q> * p::avl2<n1, S1> * q::avl2<n2, S2> & n3 + n2 =meld n1 & n1 >= n2 & n3 <= 1 & n = n1+1 & S = union(S1, S2, {v})
	or self::node<v, n, p, q> * p::avl2<n1, S1> * q::avl2<n2, S2> & n3 + n2 = n1 & n1 < n2 & n3 >= -1 & n = n2+1 & S = union(S1, S2, {v})
	inv n >= 0;*/

/* function to return the height of an avl tree */
int height(node x)
	requires x::avl2<n, S>
	ensures x::avl2<n, S> & res = n;	
{
	if (x == null)
		return 0;
	else
		return x.height;
}

/*  function to rotate left */
node rotate_left(node l, node rl, node rr)

	requires l::avl2<ln, S1> * rl::avl2<ln, S2> * rr::avl2<ln+1, S3>
	ensures res::avl2<2+ln, S> & S = union (S1,S2,S3); 

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
	requires ll::avl2<lln, S1> * lr::avl2<lln-1, S2> * r::avl2<lln-1, S3>
	ensures res::avl2<lln+1, S> & S = union (S1,S2,S3); 
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
	requires a::avl2<an, S1> * b::avl2<bn, S2> * c::avl2<cn, S3> * d::avl2<an, S4> & an = max(bn, cn) 
	         & -1 <= bn - cn <= 1
	ensures res::avl2<an + 2, S> &
	S = union(S1, S2, S3, S4, {v1}, {v2}, {v3});

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
	requires a::avl2<an, S1> * b::avl2<bn, S2> * c::avl2<cn, S3> * d::avl2<an, S4> 
	         & an = max(bn, cn) & -1 <= cn - bn <= 1
	ensures res::avl2<2 + an, S> & 
	S = union(S1, S2, S3, S4, {v1}, {v2}, {v3});

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
	requires x::avl2<n1, S1>
	ensures res::avl2<n2, S2> & S2 = union(S1, {a}) & n1<=n2 & n2<=n1+1 ;
{
	node tmp, tmp_null = null;

	if (x == null)
		{
    assume false;
    return new node (a, 1, null, null);
    }
	else 
	{ 
		if (a <= x.val)
		{// assume false;
			tmp = x.left;
			x.left = insert(tmp, a);
			// check if we need rotation 
			if ((height(x.left) - height(x.right)) == 2)
			{
				if (height(x.left.left) > height(x.left.right))
				{
					
          dprint;
          node t = rotate_right(x.left.left, x.left.right, x.right);
          return t;
				}
				else
				{ assume false;
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
		{ assume false;
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




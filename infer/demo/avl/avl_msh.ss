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
	or self::node<_, n, p, q> * p::avl<m1, n1> * q::avl<m2, n2> & m = 1+m1+m2 &
        n2<=n1+1 & n1<=n2+1 & n = max(n1, n2) + 1
	inv m >= 0 & n >= 0;

/* function to return the height of an avl tree */
int height1(node x)
	requires x::avl<m, n>
  ensures x::avl<m, n> & res = n;
{
	if (x == null)
      return 0;
	else
      return x.height;
}

int height(node x)
	requires x::avl<m, n>
  ensures x::avl<m, n> & res = n;

/*  function to rotate left */
node rotate_left1(node l, node rl, node rr)
  requires l::avl<lm, ln> * rl::avl<rlm, ln> * rr::avl<rrm, ln+1>
  ensures res::avl<2+lm+rlm+rrm, 2+ln>;

node rotate_left(node l, node rl, node rr)
  infer @post []
  requires l::avl<lm, ln> * rl::avl<rlm, ln> * rr::avl<rrm, ln+1>
  ensures res::avl<k, ln+2>;
{
	node tmp;
	int v = 10, h;

	h = height(l) + 1;
	tmp = new node(v, h, l, rl);
	h = h + 1;
	return new node(v, h, tmp, rr);
}


/* function to rotate right */
node rotate_right1(node ll, node lr, node r)
  requires ll::avl<llm, lln> * lr::avl<lrm, lln - 1> * r::avl<rm, lln - 1>
  ensures res::avl<2 + llm + lrm + rm, 1 + lln>;

node rotate_right(node ll, node lr, node r)
  infer @post []
  requires ll::avl<llm, lln> * lr::avl<lrm, lln - 1> * r::avl<rm, lln - 1>
  ensures res::avl<k, 1 + lln>;
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

int get_max1(int a , int b)
  infer @post []
  requires true
  ensures true;
{
	if (a >= b)
		return a;
	else
		return b;
}

/* double left rotation */
node rotate_double_left1(node a, node b, node c, node d, int v1, int v2, int v3)
  requires a::avl<am, an> * b::avl<bm, bn> * c::avl<cm, cn> * d::avl<dm, an> & an = max(bn, cn)
     & -1 <= bn - cn <= 1
  ensures res::avl<3 + am + bm + cm + dm, an + 2>;

node rotate_double_left(node a, node b, node c, node d, int v1, int v2, int v3)
  infer @post []
  requires a::avl<am, an> * b::avl<bm, bn> * c::avl<cm, cn> * d::avl<dm, an>
  & an = max(bn, cn) & -1 <= bn - cn <= 1
     ensures res::avl<k, an + 2>;
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
node rotate_double_right1(node a, node b, node c, node d, int v1, int v2, int v3)
  requires a::avl<am, an> * b::avl<bm, bn> * c::avl<cm, cn> * d::avl<dm, an>
  & an = max(bn, cn) & -1 <= cn - bn <= 1
     ensures res::avl<3 + am + bm + cm + dm, 2 + an>;

node rotate_double_right(node a, node b, node c, node d, int v1, int v2, int v3)
  infer @post []
  requires a::avl<am, an> * b::avl<bm, bn> * c::avl<cm, cn> * d::avl<dm, an>
  & an = max(bn, cn) & -1 <= cn - bn <= 1
     ensures res::avl<k, 2 + an>;
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
  infer @post []
  requires x::avl<mx, nx1> * y::avl<my, nx1> & x != null
  ensures res::avl<k, 1 + nx>;
{
	int v = 0;
	int tmp;

	tmp = x.height;
	tmp = tmp + 1;
	return new node(v, tmp, x, y);
}

void build_avl2(ref node x, node y, node z)
  infer @post []
  requires y::avl<my, ny> * z::avl<mz, ny> * x::node<_, _, _, _> & y != null
  ensures  x'::avl<k, ny+1>;
{
	int tmp;

	x.left = y;
	x.right = z;
	x.height = y.height  + 1;
}

node node_error() 
  requires true 
  ensures false;

node insert1(node x, int a)
  requires x::avl<m, n>
  ensures res::avl<m+1, _>;

/* function to insert a node in an avl tree (using the rotate functions) */
relation INS(int a, int b).
node insert(node x, int a)
  infer[INS]
  requires x::avl<m, n>
  ensures res::avl<k, _> & INS(k,m);
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
          if ((height(x.left) - height(x.right)) == 2)
			{
              if (height(x.left.left) > height(x.left.right))
				{
                  return rotate_right1(x.left.left, x.left.right, x.right);
				}
              else
				{
                  if (height(x.left.left) == (height(x.left.right) - 1))
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
			x.right = insert(tmp, a);
			if ((height(x.right) - height(x.left)) == 2)
              {
				if (height(x.right.right) > height(x.right.left))
                  {
					return rotate_left1(x.left, x.right.left, x.right.right);
                  }
				else
                  {
					if ((height(x.right.left) - 1) == height(x.right.right))
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

/* function to insert in an avl tree (inline version) */
relation INSI(int a, int b).
node insert_inline(node x, int a)
  requires x::avl<m, n>
  ensures res::avl<m+1, n1> & n <= n1 <= n+1;
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
				{
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
				{
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
		else	
		{
          tmp = x.right;
          x.right = insert_inline(tmp, a);
          if ((height(x.right) - height(x.left)) == 2)
			{
              k1 = x.right;
              if (height(k1.right) > height(k1.left))
				{
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
				{ 
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

relation MRG1(int a, int b, int c).
relation MRG2(int a, int b).
node merge(node t1, node t2)
  infer[MRG2]
case {
      t1=null -> requires t2::avl<s2,h2> ensures res::avl<s3,h2> & MRG2(s3,s2);
      t1!=null -> requires t1::avl<s1,h1> * t2::avl<s2,h2> ensures res::avl<s1+s2,_>;
}
{
  if (t1 == null){
    return t2;
  }
  else {
    node tmp = insert1(t2, t1.val);
    node tmp1 = merge (tmp, t1.left);
    return merge(tmp1, t1.right);
  }
}


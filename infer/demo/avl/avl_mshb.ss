/* avl trees */
/* representation of a node in an avl tree */
data node {
	int val;
	int height;
	node left;
	node right;
}

/* view for avl trees */
avl2<m, n, bal> == self = null & m = 0 & n = 0 & bal=1
  or self::node<_, n, p, q> * p::avl2<m1, n1, _> * q::avl2<m2, n2, _>
		& m = 1+m1+m2 & n=1+max(n1, n2)
		& -1 <= n1-n2 <=1 & bal=n1-n2+1
  inv m >= 0 & n >= 0 & 0<=bal<=2;

/* function to return the height of an avl tree */
int height1(node x)
     requires x::avl2<m, n,b>
     ensures x::avl2<m, n,b> & res = n;

relation H(int a, int b).
int height(node x)
     infer[H]
     requires x::avl2<m, n,b>
     ensures x::avl2<m, n,b2> & res = n & H(b,b2);
{
	if (x == null)
      return 0;
	else
      return x.height;
}

/*  function to rotate left */
node rotate_left(node l, node rl, node rr)
  requires l::avl2<lm, ln,_> * rl::avl2<rlm, ln,_> * rr::avl2<rrm, ln+1,_>
  ensures res::avl2<2+lm+rlm+rrm, 2+ln,_>;
{
	node tmp;
	int v = 10, h;

	h = height1(l) + 1;
	tmp = new node(v, h, l, rl);
	h = h + 1;
	return new node(v, h, tmp, rr);
}


/* function to rotate right */
node rotate_right(node ll, node lr, node r)
  requires ll::avl2<llm, lln,_> * lr::avl2<lrm, lln - 1, _> * r::avl2<rm, lln - 1,_>
  ensures res::avl2<2 + llm + lrm + rm, 1 + lln, _>;
{
	node tmp;
	int v = 10, h;

	h = height1(r) + 1;
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
  requires a::avl2<am, an,_> * b::avl2<bm, bn,_> * c::avl2<cm, cn,_> * d::avl2<dm, an,_>
  & an = max(bn, cn) & -1 <= bn - cn <= 1
     ensures res::avl2<3 + am + bm + cm + dm, an+2,_>;
{
	node tmp1, tmp2;
	int h;

	h = get_max(height1(a), height1(b));
	h = h + 1;
	tmp1 = new node(v1, h, a, b);

	h = get_max(height1(c), height1(d));
	h = h + 1;
	tmp2 = new node(v3, h, c, d);

	h = get_max(height1(tmp1), height1(tmp2));
	h = h + 1;
	return new node(v2, h, tmp1, tmp2);
}

/* double right rotation */
node rotate_double_right(node a, node b, node c, node d, int v1, int v2, int v3)
  requires a::avl2<am, an,_> * b::avl2<bm, bn,_> * c::avl2<cm, cn,_> * d::avl2<dm, an,_>
  & an = max(bn, cn) & -1 <= cn - bn <= 1
     ensures res::avl2<3 + am + bm + cm + dm, 2+an,_>;
{
	node tmp1, tmp2;
	int h;

	h = get_max(height1(a), height1(b));
	h = h + 1;
	tmp1 = new node(v3, h, a, b);

	h = get_max(height1(c), height1(d));
	h = h + 1;
	tmp2 = new node(v1, h, c, d);

	h = get_max(height1(tmp1), height1(tmp2));
	h = h + 1;
	return new node(v2, h, tmp1, tmp2);
}


/* functions to build avl trees */
node build_avl1(node x, node y)
  requires x::avl2<mx, nx1,_> * y::avl2<my, nx1,_> & x != null
  ensures res::avl2<1 + mx + my, 1 + nx,_>;
{
	int v = 0;
	int tmp;

	tmp = x.height;
	tmp = tmp + 1;
	return new node(v, tmp, x, y);
}

void build_avl2(ref node x, node y, node z)
  requires y::avl2<my, ny,_> * z::avl2<mz, ny,_> * x::node<_, _, _, _> & y != null
  ensures  x'::avl2<1 + my + mz, ny+1,_>;
{
	int tmp;

	x.left = y;
	x.right = z;
	x.height = y.height  + 1;
}

node node_error() requires true ensures false;

node insert1(node x, int a)
case {
    x=null ->
      ensures res::avl2<1,1,1>;
   x!=null ->
      requires x::avl2<tm, tn, b>
      ensures res::avl2<tm+1, resn, resb> & tm>0 &tn>0 &
     (tn=resn | resn=tn+1 & resb!=1);
  }

/* function to insert a node in an avl tree (using the rotate functions) */
relation INS( int c).
relation INS1( int c).
node insert(node x, int a)
  infer[INS, INS1]
case {
    x=null ->
      ensures res::avl2<1,1,b> & INS1(b);
   x!=null ->
      requires x::avl2<tm, tn, b>
      ensures res::avl2<tm+1, resn, resb> & tm>0 &tn>0 &
     (tn=resn | resn=tn+1 & INS(resb));
  }
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
          if ((height1(x.left) - height1(x.right)) == 2)
			{
              if (height1(x.left.left) > height1(x.left.right))
				{
                  return rotate_right(x.left.left, x.left.right, x.right);
				}
              else
				{
                  if (height1(x.left.left) == (height1(x.left.right) - 1))
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
			if ((height1(x.right) - height1(x.left)) == 2)
              {
				if (height1(x.right.right) > height1(x.right.left))
                  {
					return rotate_left(x.left, x.right.left, x.right.right);
                  }
				else
                  {
					if ((height1(x.right.left) - 1) == height1(x.right.right))
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
relation INSI( int c).
node insert_inline(node x, int a)
  infer[INSI]
case {
    x=null ->
      ensures res::avl2<1,1,b> & INSI(b);
   x!=null ->
      requires x::avl2<tm, tn, b>
      ensures res::avl2<tm+1, resn, resb> & tm>0 &tn>0 &
     (tn=resn | resn=tn+1 & resb!=1);
  }
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
          if ((height1(x.left) - height1(x.right)) == 2)
			{
              k1 = x.left;
              if (height1(k1.left) > height1(k1.right))
				{
                  x.left = k1.right;
                  h = get_max(height1(k1.right), height1(x.right));
                  k1.right = x;
                  h = h + 1;
                  x.height = h;
                  h = get_max(height1(k1.left), h);
                  h = h + 1;
                  k1.height = h;
                  return k1;
				}
              else
				{
                  if (height1(k1.left) == (height1(k1.right) - 1))
					{
                      k2 = k1.right;
                      x.left = k2.right;
                      k1.right = k2.left;
                      hr = height1(k2.left);
                      k2.left = k1;
                      hlt = height1(k2.right);
                      k2.right = x;

                      hl = height1(k1.left);
                      h = get_max(hl, hr);
                      h = h + 1;
                      k1.height = h;

                      hr = height1(x.right);
                      h = get_max(hlt, hr);
                      h = h + 1;
                      x.height = h;

                      h = get_max(height1(k1), x.height);
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
          if ((height1(x.right) - height1(x.left)) == 2)
			{
              k1 = x.right;
              if (height1(k1.right) > height1(k1.left))
				{
                  x.right = k1.left;
                  hr = height1(k1.left);
                  k1.left = x;

                  hl = height1(x.left);
                  h = get_max(hr, hl);
                  h = h + 1;
                  x.height = h;

                  hr = height1(k1.right);
                  h = get_max(height1(x), hr);
                  h = h + 1;
                  k1.height = h;

                  return k1;
				}
              else
				{ 
                  if ((height1(k1.left) - 1) == height1(k1.right))
					{
                      k2 = k1.left;

                      x.right = k2.left;
                      k1.left = k2.right;
                      hr = height1(k2.left);
                      k2.left = x;
                      hlt = height1(k2.right);
                      k2.right = k1;

                      hl = height1(x.left);
                      h = get_max(hl, hr);
                      h = h + 1;
                      x.height = h;

                      hr = height1(k1.right);
                      h = get_max(hlt, hr);
                      h = h + 1;
                      k1.height = h;

                      h = get_max(height1(x), height1(k1));
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

relation MRG1(int a, int b).
node merge(node t1, node t2)
  infer[MRG1]
  requires t2::avl2<s2,h2,b2>
case {
  t1=null -> ensures res::avl2<s2,h2,b3> & MRG1(b2,b3);
  t1!=null -> requires t1::avl2<s1,h1,_>  ensures res::avl2<s1+s2,_,_>;
}

{
 if (t1 == null) return t2;
    else {
	  node tmp = insert1(t2, t1.val);
	  node tmp1 = merge (tmp, t1.left);
	  return merge(tmp1, t1.right);
	  }
}


/* avl trees */

/* representation of a node in an avl tree */
data node {
	int val;
	int height;
	node left;
	node right;
}

/* view for avl trees */
//memory safety + size
avl2<m> == self = null & m = 0
	or self::node<_, n, p, q> * p::avl2<m1> * q::avl2<m2> & m = 1+m1+m2
	inv m >= 0;

/* function to return the height of an avl tree */
int height(node x)
  infer[x]
  requires x::avl2<m>
  ensures x::avl2<m>;
{
	if (x == null)
		return 0;
	else
		return x.height;
}

/*  function to rotate left */
node rotate_left(node l, node rl, node rr)
  infer[l,rl,rr,res,k]
  requires l::avl2<lm> * rl::avl2<rlm> * rr::avl2<rrm>
  ensures res::avl2<k>;//k=2+lm+rlm+rrm; 2+lm+rlm+rrm=k & (2+lm+rlm)<=k & 0<=lm &
//0<=rrm & 0<=rlm
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
  infer[ll,lr,r,res]
  requires ll::avl2<llm> * lr::avl2<lrm> * r::avl2<rm>
  ensures res::avl2<k>;//k=2 + llm + lrm + rm
//2+llm+lrm+rm=k & (2+llm+rm)<=k & 0<=lrm & 0<=rm & 0<=llm
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
  infer[a,b,c,d]
  requires a::avl2<am> * b::avl2<bm> * c::avl2<cm> * d::avl2<dm>
// & an = max(bn, cn)   & -1 <= bn - cn <= 1
  ensures res::avl2<k>;//k=3 + am + bm + cm + dm
//3+am+bm+cm+dm=k & 0<=am & 0<=cm & (3+am+bm+cm)<=k & 0<=dm & 0<=bm
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
  infer[a,b,c,d]
  requires a::avl2<am> * b::avl2<bm> * c::avl2<cm> * d::avl2<dm>
// & an = max(bn, cn) & -1 <= cn - bn <= 1
  ensures res::avl2<k>;//k=3 + am + bm + cm + dm
//3+am+bm+cm+dm=k & 0<=am & 0<=cm & (3+am+bm+cm)<=k & 0<=dm & 0<=bm
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
  infer[x,y,res]
  requires x::avl2<mx> * y::avl2<my> & x != null
  ensures res::avl2<k>;//1 + mx + my
//1+mx+my=k & 0<=mx & 0<=my & (2+my)<=k
{
	int v = 0;
	int tmp;

	tmp = x.height;
	tmp = tmp + 1;
	return new node(v, tmp, x, y);
}

void build_avl2(ref node x, node y, node z)
   infer[x,y,z]
  requires y::avl2<my> * z::avl2<mz> * x::node<_, _, _, _> & y != null
  ensures  x'::avl2<k>;//'k=1 + my + mz
//1+my+mz=k & 0<=my & 0<=mz & (2+mz)<=k
{
	int tmp;

	x.left = y;
	x.right = z;
	x.height = y.height  + 1;
}

node node_error() requires true ensures false;

node insert1(node x, int a)
  requires x::avl2<m>
  ensures res::avl2<m+1>;//k=m+1 //(m+k)>=1

/* function to insert a node in an avl tree (using the rotate functions) */
relation INS(int a, int b).
node insert(node x, int a)
  infer[INS, x, a]
  requires x::avl2<m>
  ensures res::avl2<k> & INS(k,m);//k=m+1 //(m+k)>=1
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
relation INSL(int a, int b).
node insert_inline(node x, int a)
  infer[x,INSL]
  requires x::avl2<m>
  ensures res::avl2<k> & INSL(m,k);//m>=0 & m+1=k
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
  infer[x]
  requires x::avl<m,n> & x != null
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
			else                                                                                                    // DLR
              x = rotate_double_left(x.left, x.right.left.left, x.right.left.right, x.right.right, 1, 1, 1);
		}

		return v;
	}
}


/* function to delete a node in a an avl tree */
void delete(ref node x, int a)
  requires x::avl<m, n>
  ensures x'::avl<m - 1, n1>; //' or if m = 0 then the same
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

relation MRG1(int a, int b).
//relation MRG2(int a, int b, int c).
node merge(node t1, node t2)
  infer[MRG1, t1,t2]//, MRG2]
/*requires t2::avl<s2,h2>
case {
      t1=null -> ensures res::avl<s2,h2>;
      t1!=null -> requires t1::avl<s1,h1>  ensures res::avl<s1+s2,_>;
}*/
case {
  t1=null -> requires t2::avl2<s2> ensures res::avl2<k1> & MRG1(s2,k1);//s2=k1 & 0<=k1
  t1!=null -> requires t1::avl2<s1> * t2::avl2<s2> ensures res::avl2<s1+s2>;
  //& MRG2(s1,s2,k);
}
//requires t2::avl<s2,h2> & t1=null
//ensures res::avl<s2,h2>;
//requires t1::avl<s1,h1> * t2::avl<s2,h2> & t1!=null
//ensures res::avl<s2,h2>;

{
 if (t1 == null) return t2;
    else {
	  node tmp = insert1(t2, t1.val);
	  node tmp1 = merge (tmp, t1.left);
	  return merge(tmp1, t1.right);
	  }
}


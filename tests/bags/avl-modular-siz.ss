/* avl trees */

/* representation of a node in an avl tree */
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
avl<m> == self = null & m = 0
  or self::node<v, n, p, q> * p::avl<m1> * q::avl<m2> & m = 1+m1+m2
  inv m >= 0;

/* function to return the height of an avl tree */
int height(node x)
  requires x::avl<m>
  ensures x::avl<m>;
{
  int tmpi;
  if (x == null)
    return 0;
  else
    return x.height;
}

/*  function to rotate left */
node rotate_left(node l, node rl, node rr, int v, int vr)
  requires l::avl<lm> * rl::avl<rlm> * rr::avl<rrm>
  ensures res::avl<lm+rlm+rrm+2>;
{
  node tmp, tmp2;
  int h;
  h = height(l) + 1;
  tmp = new node(v, h, l, rl);
  h = h + 1;
  tmp2 = new node(vr, h, tmp, rr);
  return tmp2;
}

node rotate_left2(node l, node rl, node rr, int v, int vr)
  requires l::avl<lm> * rl::avl<rlm> * rr::avl<rrm>
  ensures res::avl<2+lm+rlm+rrm>;
{
  node tmp;
  int h;
  h = height(l) + 2;
  tmp = new node(v, h, l, rl);
  h = h + 1;
  return new node(vr, h, tmp, rr);
}

/* function to rotate right */
node rotate_right(node ll, node lr, node r, int vl, int v)
  requires ll::avl<llm> * lr::avl<lrm> * r::avl<rm>
  ensures res::avl<2 + llm + lrm + rm>;
{
	node tmp;
	int h;
	h = height(r) + 1;
	tmp = new node(v, h, lr, r);
	h = h + 1;
	return new node(vl, h, ll, tmp);
}

node rotate_right2(node ll, node lr, node r, int vl, int v)
  requires ll::avl<llm> * lr::avl<lrm> * r::avl<rm>
  ensures res::avl<2 + llm + lrm + rm>;
{
	node tmp;
	int h;
	h = height(r) + 2;
	tmp = new node(v, h, lr, r);
	h = h + 1;
	return new node(vl, h, ll, tmp);
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
node rotate_double_left(node a, node b, node c, node d, int v, int vrl, int vr)
  requires a::avl<am> * b::avl<bm> * c::avl<cm> * d::avl<dm>
  ensures res::avl<3 + am + bm + cm + dm>;
{
	node tmp1, tmp2;
	int h;

	h = get_max(height(a), height(b));
	h = h + 1;
	tmp1 = new node(v, h, a, b);

	h = get_max(height(c), height(d));
	h = h + 1;
	tmp2 = new node(vr, h, c, d);

	h = get_max(height(tmp1), height(tmp2));
	h = h + 1;
	return new node(vrl, h, tmp1, tmp2);
}


/* double right rotation */
node rotate_double_right(node a, node b, node c, node d, int vl, int vlr, int v)
  requires a::avl<am> * b::avl<bm> * c::avl<cm> * d::avl<dm>
  ensures res::avl<3 + am + bm + cm + dm>;
{
	node tmp1, tmp2;
	int h;

	h = get_max(height(a), height(b));
	h = h + 1;
	tmp1 = new node(vl, h, a, b);

	h = get_max(height(c), height(d));
	h = h + 1;
	tmp2 = new node(v, h, c, d);

	h = get_max(height(tmp1), height(tmp2));
	h = h + 1;
	return new node(vlr, h, tmp1, tmp2);

}

//node node_error() requires true ensures false;

/* function to insert a node in an avl tree (using the rotate functions) */
node insert(node x, int a)
  requires x::avl<m> & x != null
  ensures res::avl<m+1>;
{
  node tmpn, tmp_null = null;
  int hr, hl;
  myint ret = new myint(0);
  if (x.val <= a) {
	if (x.right == null) {
      x.right = new node (a, 1, tmp_null, tmp_null);
      if (x.left == null) {
        x.height = 2;
        return x;
      } else {
        return x;
      }
    } else if (x.left == null) {
      x.left = new node (x.val, 1, tmp_null, tmp_null);
      ret.val = a;
      x.right = remove_min_add(x.right, ret);
      x.val = ret.val;
      // TODO: Why needed?
      x.height = get_max(height(x.left), height(x.right)) + 1;
      return x;
    } else {
      if (height(x.right) <= height(x.left)) {
        x.right = insert(x.right, a);
        x.height = get_max(height(x.left), height(x.right)) + 1;
        return x;
      } else {
        x.left = insert(x.left, x.val);
        ret.val = a;
        x.right = remove_min_add(x.right, ret);
        x.val = ret.val;
        x.height = get_max(height(x.left), height(x.right)) + 1;
        return x;
      }
    }
  } else {
	if (x.left == null) {
      x.left = new node (a, 1, tmp_null, tmp_null);
      if (x.right == null) x.height = 2;
      return x;
    } else if (x.right == null) {
      x.right = new node (x.val, 1, tmp_null, tmp_null);
      ret.val = a;
      x.left = remove_max_add(x.left, ret);
      x.val = ret.val;
      // TODO: Why needed?
      x.height = get_max(height(x.left), height(x.right)) + 1;
      return x;
    } else {
      if (height(x.left) <= height(x.right)) {
        x.left = insert(x.left, a);
        x.height = get_max(height(x.left), height(x.right)) + 1;
        return x;
      } else {
        x.right = insert(x.right, x.val);
        ret.val = a;
        x.left = remove_max_add(x.left, ret);
        x.val = ret.val;
        x.height = get_max(height(x.left), height(x.right)) + 1;
        return x;
      }
    }
  }
}

node remove_min_add(node x, ref myint a)
  requires x::avl<m> * a::myint<vv> & x != null
  ensures res::avl<m> * a'::myint<r>; //'  Unable to prove: r <= vv
{
  int ti;
  node tn;
  node tr;
  myint tmp2 = new myint(0);
  if (x.left == null) {
    if (x.right == null) {
      if (a.val >= x.val) {
        ti = x.val;
        x.val = a.val;
        a.val = ti;
        return x;
      } else {
        return x;
      }
    } else {
      if (x.right.val >= a.val) {
        if (a.val >= x.val) {
          ti = x.val;
          x.val = a.val;
          a.val = ti;
          ti = x.val;
          tr = x.right.left;
          assume tr' = null; //'
          return x;
        } else {
          return x;
        }
      } else {
        ti = x.val;
        tr = x.right.left;
        assume tr' = null;
        tr = x.right.right;
        assume tr' = null;
        x.val = x.right.val;
        x.right.val = a.val;
        a.val = ti;
        return x;
      }
    }
  } else {
    if (a.val >= x.val) {
      if (x.right == null) {
        tr = x.left.left;
        assume tr' = null; //'
        tr = x.left.right;
        assume tr' = null; //'
        ti = x.left.val;
        x.left.val = x.val;
        x.val = a.val;
        a.val = ti;
        return x;
      } else {
        x.right = remove_min_add(x.right, a);
        ti = a.val;
        a.val = x.val;
        x.left = remove_min_add(x.left, a);
        x.val = ti;
        return x;
      }
    } else {
      tn = x.left;
      ti = x.val;
      x.left = remove_min_add(x.left, a);
      return x;
    }
  }
}

node remove_max_add(node x, ref myint a)
  requires x::avl<m> * a::myint<vv> & x != null
  ensures res::avl<m> * a'::myint<r>; //'  & r >= vv
{
  int ti;
  myint ti2 = new myint(0);
  node tr;
  node tn;
  myint tmp2;
  if (x.right == null) {
   if (x.left == null) {
      if (a.val <= x.val) {
        ti = x.val;
        x.val = a.val;
        a.val = ti;
        return x;
      } else {
        return x;
      }
    } else {
      if (x.left.val <= a.val) {
        if (a.val <= x.val) {
          ti = x.val;
          x.val = a.val;
          a.val = ti;
          ti = x.val;
          tr = x.left.right;
          assume tr' = null; //'
          return x;
        } else {
          return x;
        }
      } else {
        ti = x.val;
        tr = x.left.right;
        assume tr' = null;
        tr = x.left.left;
        assume tr' = null;
        x.val = x.left.val;
        x.left.val = a.val;
        a.val = ti;
        return x;
      }
    }
  } else {
    if (a.val <= x.val) {
      if (x.left == null) {
        tr = x.right.right;
        assume tr' = null; //'
        tr = x.right.left;
        assume tr' = null; //'
        ti = x.right.val;
        x.right.val = x.val;
        x.val = a.val;
        a.val = ti;
        return x;
      } else {
        x.left = remove_max_add(x.left, a);
        ti = a.val;
        a.val = x.val;
        x.right = remove_max_add(x.right, a);
        x.val = ti;
        return x;
      }
    } else {
      tn = x.right;
      ti = x.val;
      x.right = remove_max_add(x.right, a);
      return x;
    }
  }
}

/* function to delete the smallest element in an avl tree */
node remove_min(node x, ref myint a)
    requires x::avl<m> * a::myint<_> & x != null
    ensures res::avl<m - 1> * a'::myint<r>; //'
{
  myint ret = new myint(0),tmp = new myint(0);
  node tn;
  //int hl, hr;
  if (x.left == null) {
    a.val = x.val;
    return x.right;
  } else {
    if (height(x.left) < height(x.right)) {
      tn = x.right;
      assume tn' != null; //'
      dprint;
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

/* function to delete the top node in a an avl tree */
node delete_top(node x)
  requires x::node<v, n, p, q> * p::avl<m1> * q::avl<m2>
  ensures res::avl<m1+m2>;
{
  node tmp;
  myint ti = new myint(0);

  if (x.right == null) {
    return (x.left);
  } else if (x.left == null) {
    return (x.right);
  } else {
    x.right = remove_min(x.right, ti);
    x.val = ti.val;
    //rebalance
    if ((height(x.left) - height(x.right)) == 2) {
      if ((height(x.left.left) - 1) == height(x.left.right)) {
        x = rotate_right(x.left.left, x.left.right, x.right, x.left.val, x.val); // SRR
        return x;
      } else if (height(x.left.left) == height(x.left.right)) {
        x = rotate_right2(x.left.left, x.left.right, x.right, x.left.val, x.val); // SRR
        return x;
      } else {
        tmp = x.left;
        assume tmp' != null; //'
        tmp = x.left.right;
        assume tmp' != null; //'
        tmp = rotate_double_right(x.left.left, x.left.right.left, x.left.right.right, x.right, x.left.val, x.left.right.val, x.val); // DRR
        return tmp;
      }
    } else {
      x.height = get_max(height(x.left), height(x.right)) + 1;
      return x;
    }
  }
}

/* function to delete a node in a an avl tree */
node delete(node x, int a)
  requires x::avl<m>
  ensures res::avl<mm> & m <= mm + 1 & mm <= m;
{
  node tmp;
  if (x == null) return x; else {
  if (x.val == a)
    return delete_top (x);
  else if (x.val < a) {
    if (x.right == null)
      return x;
    else {
      x.right = delete(x.right, a);
      if ((height(x.left) - height(x.right)) == 2) {
        tmp = x.left;
        assume tmp'!=null; //'
        if ((height(x.left.left) - 1) == height(x.left.right)) {
          x = rotate_right(x.left.left, x.left.right, x.right, x.left.val, x.val); // SRR
          return x;
        } else if (height(x.left.left) == height(x.left.right)) {
          x = rotate_right2(x.left.left, x.left.right, x.right, x.left.val, x.val); // SRR
          return x;
        } else {
          tmp = x.left.right;
          assume tmp'!=null; //'
          tmp = rotate_double_right(x.left.left, x.left.right.left, x.left.right.right, x.right, x.left.val, x.left.right.val, x.val); // DRR
          return tmp;
        }
      } else {
        x.height = get_max(height(x.left), height(x.right)) + 1;
        return x;
      }
    }
  } else {
    if (x.left == null)
      return x;
    else {
      x.left = delete(x.left, a);
      if ((height(x.right) - height(x.left)) == 2) {
        tmp = x.right;
        assume tmp'!=null; //'
        if ((height(x.right.left)) == height(x.right.right) - 1) {
          x = rotate_left(x.left, x.right.left, x.right.right, x.val, x.right.val); // SRR
          return x;
        } else if (height(x.right.left) == height(x.right.right)) {
          x = rotate_left2(x.left, x.right.left, x.right.right, x.val, x.right.val); // SRR
          return x;
        } else {
          tmp = x.right.left;
          assume tmp'!=null; //'
          tmp = rotate_double_left(x.left, x.right.left.left, x.right.left.right, x.right.right, x.val, x.right.left.val, x.right.val); // DRR
          return tmp;
        }
      } else {
        x.height = get_max(height(x.left), height(x.right)) + 1;
        return x;
      }
    }
  }
  }
}

void main()
  requires true ensures true;
{
  node tmp = new node(1,1,null,null);
  tmp=insert(tmp, 3);
  tmp=insert(tmp, 11);
  tmp=insert(tmp, 5);
  tmp=insert(tmp, 7);
  tmp=insert(tmp, 9);
  tmp=delete(tmp,3);
  tmp=delete(tmp,7);
  tmp=delete(tmp,9);
  tmp=delete(tmp,11);
}

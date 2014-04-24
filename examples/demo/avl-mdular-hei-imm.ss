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
avl<n> == self = null & n = 0
  or self::node<v, n, p, q> * p::avl<n1> * q::avl<n2> &
  -1 <= n1-n2 <= 1 & n=1+max(n1, n2) 
  inv n >= 0;

/* function to return the height of an avl tree */
int height(node x)
  requires x::avl<n>@I
  ensures res = n;
{
  int tmpi;
  if (x == null)
    return 0;
  else
    return x.height;
}

node copy(node x) 
requires x::avl<n>@I
ensures res::avl<n>;
{
 node tmp1, tmp2;
 if (x==null) return null;
    else {
	  tmp1 = copy(x.left);
	  tmp2 = copy(x.right); 
	  return new node(x.val, x.height, tmp1, tmp2);
	      }
}

/*  function to rotate left */
node rotate_left(node l, node rl, node rr, int v, int vr)
  requires (l::avl<ln>@I & rl::avl<ln>@I & rr::avl<ln+1>@I)
  & v <= vr
  ensures res::avl<2+ln>;
{
  node tmp, tmp2;
  int h;
  h = height(l) + 1;
  tmp = new node(v, h, copy(l), copy(rl));
  h = h + 1;
  tmp2 = new node(vr, h, tmp, copy(rr));
  return tmp2;
}

node rotate_left2(node l, node rl, node rr, int v, int vr)
  requires (l::avl<ln>@I & rl::avl<ln+1>@I & rr::avl<ln+1>@I)
  ensures res::avl<3+ln>;
{
  node tmp;
  int h;
  h = height(l) + 2;
  tmp = new node(v, h, copy(l), copy(rl));
  h = h + 1;
  return new node(vr, h, tmp, copy(rr));
}

/* function to rotate right */
node rotate_right(node ll, node lr, node r, int vl, int v)
  requires (ll::avl<lln>@I & lr::avl<lln - 1>@I & r::avl<lln - 1>@I)
  ensures res::avl<1 + lln>;
{
	node tmp;
	int h;
	h = height(r) + 1;
	tmp = new node(v, h, copy(lr), copy(r));
	h = h + 1;
	return new node(vl, h, copy(ll), tmp);
}

node rotate_right2(node ll, node lr, node r, int vl, int v)
  requires (ll::avl<lln>@I & lr::avl<lln>@I & r::avl<lln - 1>@I)
  ensures res::avl<2 + lln>;
{
	node tmp;
	int h;
	h = height(r) + 2;
	tmp = new node(v, h, copy(lr), copy(r));
	h = h + 1;
	return new node(vl, h, copy(ll), tmp);
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
  requires (a::avl<an>@I & b::avl<bn>@I & c::avl<cn>@I & d::avl<an>@I)
    & an = max(bn, cn) & cn <= bn + 1 & bn <= cn + 1 // & -1 <= bn - cn <= 1
  ensures res::avl<an + 2>;
{
	node tmp1, tmp2;
	int h;

	h = get_max(height(a), height(b));
	h = h + 1;
	tmp1 = new node(v, h, copy(a), copy(b));

	h = get_max(height(c), height(d));
	h = h + 1;
	tmp2 = new node(vr, h, copy(c), copy(d));

	h = get_max(height(tmp1), height(tmp2));
	h = h + 1;
	return new node(vrl, h, tmp1, tmp2);
}


/* double right rotation */
node rotate_double_right(node a, node b, node c, node d, int vl, int vlr, int v)
  requires (a::avl<an>@I & b::avl<bn>@I & c::avl<cn>@I & d::avl<an>@I)
    & an = max(bn, cn) & cn <= bn + 1 & bn <= cn + 1 // & -1 <= bn - cn <= 1
  ensures res::avl<2 + an>;
{
	node tmp1, tmp2;
	int h;

	h = get_max(height(a), height(b));
	h = h + 1;
	tmp1 = new node(vl, h, copy(a), copy(b));

	h = get_max(height(c), height(d));
	h = h + 1;
	tmp2 = new node(v, h, copy(c), copy(d));

	h = get_max(height(tmp1), height(tmp2));
	h = h + 1;
	return new node(vlr, h, tmp1, tmp2);

}

//node node_error() requires true ensures false;

/* function to insert a node in an avl tree (using the rotate functions) */
node insert(node x, int a)
  requires x::avl<n>@I & x != null
  ensures res::avl<nn> & n <= nn <= n+1;
{
  node tmp_x;
  node tmpn, tmp_null = null;
  int hr, hl;
  tmp_x = copy(x);
  myint ret = new myint(0);
  if (tmp_x.val <= a) {
	if (tmp_x.right == null) {
      tmp_x.right = new node (a, 1, tmp_null, tmp_null);
      if (tmp_x.left == null) {
        tmp_x.height = 2;
        return tmp_x;
      } else {
        return tmp_x;
      }
    } else if (tmp_x.left == null) {
      tmp_x.left = new node (tmp_x.val, 1, tmp_null, tmp_null);
      ret.val = a;
      tmp_x.right = remove_min_add(tmp_x.right, ret);
      tmp_x.val = ret.val;
      // TODO: Why needed?
      tmp_x.height = get_max(height(tmp_x.left), height(tmp_x.right)) + 1;
      return tmp_x;
    } else {
      if (height(tmp_x.right) <= height(tmp_x.left)) {
        tmp_x.right = insert(tmp_x.right, a);
        tmp_x.height = get_max(height(tmp_x.left), height(tmp_x.right)) + 1;
        return tmp_x;
      } else {
        tmp_x.left = insert(tmp_x.left, tmp_x.val);
        ret.val = a;
        tmp_x.right = remove_min_add(tmp_x.right, ret);
        tmp_x.val = ret.val;
        tmp_x.height = get_max(height(tmp_x.left), height(tmp_x.right)) + 1;
        return tmp_x;
      }
    }
  } else {
	if (tmp_x.left == null) {
      tmp_x.left = new node (a, 1, tmp_null, tmp_null);
      if (tmp_x.right == null) tmp_x.height = 2;
      return tmp_x;
    } else if (tmp_x.right == null) {
      tmp_x.right = new node (tmp_x.val, 1, tmp_null, tmp_null);
      ret.val = a;
      tmp_x.left = remove_max_add(tmp_x.left, ret);
      tmp_x.val = ret.val;
      // TODO: Why needed?
      tmp_x.height = get_max(height(tmp_x.left), height(tmp_x.right)) + 1;
      return tmp_x;
    } else {
      if (height(tmp_x.left) <= height(tmp_x.right)) {
        tmp_x.left = insert(tmp_x.left, a);
        tmp_x.height = get_max(height(tmp_x.left), height(tmp_x.right)) + 1;
        return tmp_x;
      } else {
        tmp_x.right = insert(tmp_x.right, tmp_x.val);
        ret.val = a;
        tmp_x.left = remove_max_add(tmp_x.left, ret);
        tmp_x.val = ret.val;
        tmp_x.height = get_max(height(tmp_x.left), height(tmp_x.right)) + 1;
        return tmp_x;
      }
    }
  }
}

node remove_min_add(node y, ref myint a)
  requires y::avl<n>@I * a::myint<vv> & y != null
  ensures res::avl<n> * a'::myint<r> & r <= vv; //'
{
  int ti, ti2;
  node tn;
  node tr;
  node x = copy(y);

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
          //assert tr' = null; //'
          return x;
        } else {
          return x;
        }
      } else {
        ti = x.val;
        tr = x.right.left;
        //assert tr' = null;
        tr = x.right.right;
        //assert tr' = null;
        x.val = x.right.val;
        x.right.val = a.val;
        a.val = ti;
        ti2 = x.right.val;
        assume ti' <= ti2';
        return x;
      }
    }
  } else {
    if (a.val >= x.val) {
      if (x.right == null) {
        tr = x.left.left;
        //assert tr' = null; //'
        tr = x.left.right;
        //assert tr' = null; //'
        ti = x.left.val;
        x.left.val = x.val;
        x.val = a.val;
        a.val = ti;
        ti2 = x.val;
        assume ti' <= ti2';
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

node remove_max_add(node y, ref myint a)
  requires y::avl<n>@I * a::myint<vv> & y != null
  ensures res::avl<n> * a'::myint<r>; //'  & r >= vv
{
  int ti;
  myint ti2 = new myint(0);
  node tr;
  node tn;
  myint tmp2;
  node x = copy(y);

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
          //assert tr' = null; //'
          return x;
        } else {
          return x;
        }
      } else {
        ti = x.val;
        tr = x.left.right;
        //assert tr' = null; //'
        tr = x.left.left;
        //assert tr' = null; //'
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
        //assert tr' = null; //'
        tr = x.right.left;
        //assert tr' = null; //'
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
node remove_min(node y, ref myint a)
    requires y::avl<n>@I * a::myint<_> & y != null
    ensures res::avl<nn> * a'::myint<r> & n-1 <= nn <= n; //'
{
  node x = copy(y);
  myint ret = new myint(0),tmp = new myint(0);
  node tn;
  //int hl, hr;
  if (x.left == null) {
    a.val = x.val;
    return x.right;
  } else {
    if (height(x.left) < height(x.right)) {
      tn = x.right;
      //assert tn' != null; //'
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

/* function to delete the top node in an avl tree */
node delete_top(node y)
  requires y::node<v, n, py, qy>@I * py::avl<n1>@I * qy::avl<n2>@I
    & n <= n1 + 2 & n <= n2 + 2 & exists (tmps : tmps=max(n1, n2) & n = tmps + 1)
  ensures res::avl<nn> & n <= nn + 1 & nn <= n;
{
  node tmp;
  myint ti = new myint(0);
  node x = copy(y);
  node p = x.left;
  node q = x.right;

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
        //assert tmp' != null; //'
        tmp = x.left.right;
        //assert tmp' != null; //'
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
node delete(node y, int a)
  requires y::avl<n>@I
  ensures res::avl<nn> & n <= nn + 1 & nn <= n;
{
  int ti1, ti2;
  node tmp;
  node x = copy(y);  

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
        //assert tmp'!=null; //'
        if ((height(x.left.left) - 1) == height(x.left.right)) {
          x = rotate_right(x.left.left, x.left.right, x.right, x.left.val, x.val); // SRR
          return x;
        } else if (height(x.left.left) == height(x.left.right)) {
          x = rotate_right2(x.left.left, x.left.right, x.right, x.left.val, x.val); // SRR
          return x;
        } else {
          tmp = x.left.right;
          //assert tmp'!=null; //'
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
        //assert tmp'!=null; //'
        if ((height(x.right.left)) == height(x.right.right) - 1) {
          ti1 = x.val;
          ti2 = x.right.val;
          assume ti1' <= ti2';
          x = rotate_left(x.left, x.right.left, x.right.right, x.val, x.right.val); // SRR
          return x;
        } else if (height(x.right.left) == height(x.right.right)) {
          x = rotate_left2(x.left, x.right.left, x.right.right, x.val, x.right.val); // SRR
          return x;
        } else {
          tmp = x.right.left;
          //assert tmp'!=null; //'
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

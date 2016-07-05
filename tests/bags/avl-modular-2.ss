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
avl<"m":m, "n":n, "S":S> == 
  self = null & [
    "m":m = 0; 
    "n": n = 0; 
    "S": S = {}]
  or self::node<v, n, p, q> * p::avl<m1, n1, S1> * q::avl<m2, n2, S2> & [
    "m" : m = 1+m1+m2 ; 
    "n" : -1 <= n1 - n2 <= 1 & n = 1 + max(n1, n2) ;
    "S" : S = union(S1, S2, {v}) & forall (x : (x notin S1 | x <= v)) & forall (y : (y notin S2 | y >= v))]
  inv true & [
    "m" : m >= 0;
    "n" : n >= 0];

  // n <= n1 + 2 & n <= n2 + 2 & tmp=max(n1, n2) & n = tmp + 1 & 

/* function to return the height of an avl tree */
int height(node x)
  requires x::avl<m, n, S>
  ensures x::avl<m, n, S> & ["n" : res = n];
{
  int tmpi;
  if (x == null)
    return 0;
  else
    return x.height;
}

int get_max_height_add1(node x, node y)
  requires x::avl<m,n,S>*y::avl<m2,n2,S2>
  ensures x::avl<m,n,S>*y::avl<m2,n2,S2> & ["n" : res=max(n,n2)+1];
{
  return 1+get_max(height(x),height(y));
}


bool lesseq_h(node x, node y)
  requires x::avl<m,n,S>*y::avl<m2,n2,S2>
  ensures x::avl<m,n,S>*y::avl<m2,n2,S2> 
         & ["n" : 
           (res & n<=n2 
           | !res & n>n2) ];
{
  return height(x)<=height(y);
}

bool less_h(node x, node y)
  requires x::avl<m,n,S>*y::avl<m2,n2,S2>
  ensures x::avl<m,n,S>*y::avl<m2,n2,S2> 
         & ["n" : (res & n<n2 | !res & n>=n2) ];
{
  return height(x)<height(y);
}

bool eq_h(node x, node y)
  requires x::avl<m,n,S>*y::avl<m2,n2,S2>
  ensures x::avl<m,n,S>*y::avl<m2,n2,S2> 
         & ["n" : (res & n=n2 | !res & n!=n2) ];
{
  return height(x)==height(y);
}

bool diff_h_by_1(node x, node y)
  requires x::avl<m,n,S>*y::avl<m2,n2,S2>
  ensures x::avl<m,n,S>*y::avl<m2,n2,S2> 
         & ["n" : (res & n=n2+1 | !res & n!=n2+1) ];
{
  return height(x)==height(y)+1;
}

bool diff_h_by_2(node x, node y)
  requires x::avl<m,n,S>*y::avl<m2,n2,S2>
  ensures x::avl<m,n,S>*y::avl<m2,n2,S2> 
         & ["n" : (res & n=n2+2 | !res & n!=n2+2) ];
{
  return height(x)==height(y)+2;
}


/*  function to rotate left */
node rotate_left(node l, node rl, node rr, int v, int vr)
  requires l::avl<lm, ln, Sl> * rl::avl<rlm, rln, Srl> * rr::avl<rrm, rn, Srr> & [
  "S" : forall (x : (x notin Sl | x <= v)) & forall (y : (y notin Srl | y >= v))
      & forall (z : (z notin Srl | z <= vr)) & forall (w : (w notin Srr | w >= vr)) & v <= vr;
  "n" : rn=ln+1 & rln >= ln & rln <= ln + 1]
  ensures res::avl<nm, nn, S> &
   ["S" : S = union(Sl, Srl, Srr, {v,vr});
    "m" : nm = lm+rlm+rrm+2;
    "n" : nn = 2+rln];
{
  node tmp, tmp2;
  int h;
  h = height(rl) + 1;
  tmp = new node(v, h, l, rl);
  h = h + 1;
  tmp2 = new node(vr, h, tmp, rr);
  return tmp2;
}

/* function to rotate right */
node rotate_right(node ll, node lr, node r, int vl, int v)
  requires ll::avl<llm, lln, Sll> * lr::avl<lrm, lrn, Slr> * r::avl<rm, rn, Sr> & [
  "S" : forall (x : (x notin Sll | x <= vl)) & forall (y : (y notin Slr | y >= vl))
    & forall (z : (z notin Slr | z <= v)) & forall (w : (w notin Sr | w >= v)) & vl <= v;
  "n" : rn=lln-1 & lrn <= lln & lln <= lrn + 1]
  ensures res::avl<nm, nn, S> &
   ["S" : S = union(Sll,Slr,Sr,{vl,v});
    "m" : nm = llm+lrm+rm+2;
    "n" : nn = 2+lrn];
{
  node tmp;
  int h;
  h = height(lr) + 1;
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
  requires a::avl<am, an, Sl> * b::avl<bm, bn, Srll> * c::avl<cm, cn, Srlr> * d::avl<dm, an, Srr>
  & ["S" : forall (x : (x notin Sl | x <= v)) & forall (y : (y notin Srll | y >= v))
    & forall (z : (z notin Srll | z <= vrl)) & forall (w : (w notin Srlr | w >= vrl))
    & forall (xx : (xx notin Srlr | xx <= vr)) & forall (yy : (yy notin Srr | yy >= vr))
     & v <= vrl <= vr; "n" : an = max(bn, cn) & cn <= bn + 1 & bn <= cn + 1] // & -1 <= bn - cn <= 1
  ensures res::avl<nm, nn, S> & 
    ["S" : S = union(Sl,Srll,Srlr,Srr,{v,vrl,vr}); "m" : nm = 3 + am + bm + cm + dm; "n" : nn = an + 2];
{
	node tmp1, tmp2;
	int h;

	h = get_max_height_add1(a, b);
	//h = h + 1;
	tmp1 = new node(v, h, a, b);

	h = get_max_height_add1(c,d);
	//h = h + 1;
	tmp2 = new node(vr, h, c, d);

	h = get_max_height_add1(tmp1, tmp2);
	//h = h + 1;
	return new node(vrl, h, tmp1, tmp2);
}


/* double right rotation */
node rotate_double_right(node a, node b, node c, node d, int vl, int vlr, int v)
  requires a::avl<am, an, Sll> * b::avl<bm, bn, Slrl> * c::avl<cm, cn, Slrr> * d::avl<dm, an, Sr>
  & ["S" : forall (x : (x notin Sll | x <= vl)) & forall (y : (y notin Slrl | y >= vl))
    & forall (z : (z notin Slrl | z <= vlr)) & forall (w : (w notin Slrr | w >= vlr))
    & forall (xx : (xx notin Slrr | xx <= v)) & forall (yy : (yy notin Sr | yy >= v))
     & vl <= vlr <= v; "n" : an = max(bn, cn) & cn <= bn + 1 & bn <= cn + 1] // & -1 <= bn - cn <= 1
  ensures res::avl<nm, nn, S> & [
    "m" : nm = 3 + am + bm + cm + dm;
    "n" : nn = 2 + an;
    "S" : S = union(Sll,Slrl,Slrr,Sr,{vl,vlr,v})];
{
	node tmp1, tmp2;
	int h;

	h = get_max_height_add1(a, b);
	//h = h + 1;
	tmp1 = new node(vl, h, a, b);

	h = get_max_height_add1(c,d);
	//h = h + 1;
	tmp2 = new node(v, h, c, d);

	h = get_max_height_add1(tmp1,tmp2);
	//h = h + 1;
	return new node(vlr, h, tmp1, tmp2);

}

//node node_error() requires true ensures false;

/* function to insert a node in an avl tree (using the rotate functions) */
node insert(node x, int a)
  requires x::avl<m, n, S> & x != null
  ensures res::avl<nm, nn, Sn> & ["m":nm = m + 1; "n": n <= nn <= n+1; "S" : Sn = union(S, {a})];
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
      x.height = get_max_height_add1(x.left, x.right) ;
      return x;
    } else {
      if (lesseq_h(x.right,x.left)) {
        x.right = insert(x.right, a);
        x.height = get_max_height_add1(x.left, x.right);
        return x;
      } else {
        x.left = insert(x.left, x.val);
        ret.val = a;
        x.right = remove_min_add(x.right, ret);
        x.val = ret.val;
        x.height = get_max_height_add1(x.left, x.right);
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
      x.height = get_max_height_add1(x.left, x.right);
      return x;
    } else {
      if (lesseq_h(x.left,x.right)) {
        x.left = insert(x.left, a);
        x.height = get_max_height_add1(x.left, x.right) ;
        return x;
      } else {
        x.right = insert(x.right, x.val);
        ret.val = a;
        x.left = remove_max_add(x.left, ret);
        x.val = ret.val;
        x.height = get_max_height_add1(x.left, x.right);
        return x;
      }
    }
  }
}

node remove_min_add(node x, ref myint a)
  requires x::avl<m,n,S> * a::myint<vv> & x != null
  ensures res::avl<m,n,Sn> * a'::myint<r> /*'*/ & 
    ["S" : union(S, {vv}) = union(Sn, {r}) & r <= vv & forall (xx : (xx notin Sn | r <= xx))];
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
          //assert tr' = null assume tr' = null; //'
          assume tr' = null or tr'!=null;
          return x;
        } else {
          return x;
        }
      } else {
        ti = x.val;
        tr = x.right.left;
        // assert tr' = null assume tr' = null; //'
        //assume tr' = null or tr'!=null;
        tr = x.right.right; 
        // fails! assert tr' = null assume tr' = null; //'
        //assume tr' = null or tr'!=null;
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
        //assert tr' = null assume tr' = null; //'
        //assume tr' = null or tr'!=null;
        tr = x.left.right;
        //assert tr' = null assume tr' = null; //'
        //assume tr' = null or tr'!=null;
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
  requires x::avl<m,n,S> * a::myint<vv> & x != null
  ensures res::avl<m,n,Sn> * a'::myint<r> & ["S" : union(S, {vv}) = union(Sn, {r}) & r >= vv & //'
    forall (xx : (xx notin Sn | r >= xx))];
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
          //assert tr' = null assume tr' = null; //'
	  assume tr'=null or tr'!=null;
          return x;
        } else {
          return x;
        }
      } else {
        ti = x.val;
        tr = x.left.right;
	assume tr'=null or tr'!=null;
        tr = x.left.left;
	assume tr'=null or tr'!=null;
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
	assume tr'=null or tr'!=null;
        tr = x.right.left;
	assume tr'=null or tr'!=null;
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
    requires x::avl<m, n, S> * a::myint<_> & x != null
    ensures res::avl<nm, nn, Sn> * a'::myint<r> & 
      ["m" : nm = m - 1; "n" : n-1 <= nn <= n; "S" : union(Sn, {r}) = S & forall (xx : (xx notin S | r <= xx))]; //'
{
  myint ret = new myint(0),tmp = new myint(0);
  node tn;
  //int hl, hr;
  if (x.left == null) {
    a.val = x.val;
    return x.right;
  } else {
    if (less_h(x.left,x.right)) {
      // assert x.right != null;
      tn = x.right;
      assume tn'=null or tn'!=null;
      ret.val = x.val;
      x.left = remove_min_add(x.left, ret);
      a.val = ret.val;
      x.right = remove_min(x.right, tmp);
      x.val = tmp.val;
      x.height = get_max_height_add1(x.left, x.right) ;
      return x;
    } else {
      x.left = remove_min(x.left, a);
      x.height = get_max_height_add1(x.left, x.right) ;
      return x;
    }
  }
}

/* function to delete the top node in a an avl tree */
node delete_top(node x)
  requires x::node<v, n, p, q> * p::avl<m1, n1, S1> * q::avl<m2, n2, S2>
  & ["n" : n <= n1 + 2 & n <= n2 + 2 & exists (tmps : tmps=max(n1, n2) & n = tmps + 1);
     "S" : forall (xx : (xx notin S1 | xx <= v)) & forall (y : (y notin S2 | y >= v))]
  ensures res::avl<nm, nn, Sn> & ["m": nm = m1 + m2; "S" : Sn = union(S1, S2); "n" : n <= nn + 1 & nn <= n];
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
    if (diff_h_by_2(x.left,x.right)) {
      if (diff_h_by_1(x.left.left,x.left.right)) {
        x = rotate_right(x.left.left, x.left.right, x.right, x.left.val, x.val); // SRR
        return x;
      } else if (eq_h(x.left.left,x.left.right)) {
        x = rotate_right(x.left.left, x.left.right, x.right, x.left.val, x.val); // SRR
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
      x.height = get_max_height_add1(x.left, x.right);
      return x;
    }
  }
}

/* function to delete a node in a an avl tree */
node delete(node x, int a)
  requires x::avl<m, n, S>
  ensures res::avl<mm, nn, Sn> & 
   ["n" : n-1 <= nn <= n;
    "m" : m-1 <= mm <= m; 
    "S": Sn subset S & forall (xx : (xx notin S | xx = a | xx in Sn))];
// forall xx in S . xx=a \/ xx in Sn
// forall xx .  xx in S -> xx=a \/ xx in Sn
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
      if (diff_h_by_2(x.left,x.right)) {
        tmp = x.left;
        //assert tmp'!=null; //'
        if (diff_h_by_1(x.left.left,x.left.right)) {
          x = rotate_right(x.left.left, x.left.right, x.right, x.left.val, x.val); // SRR
          return x;
        } else if (eq_h(x.left.left,x.left.right)) {
          x = rotate_right(x.left.left, x.left.right, x.right, x.left.val, x.val); // SRR
          return x;
        } else {
          tmp = x.left.right;
          //assert tmp'!=null; //'
          tmp = rotate_double_right(x.left.left, x.left.right.left, x.left.right.right, x.right, x.left.val, x.left.right.val, x.val); // DRR
          return tmp;
        }
      } else {
        x.height = get_max_height_add1(x.left, x.right) ;
        return x;
      }
    }
  } else {
    if (x.left == null)
      return x;
    else {
      x.left = delete(x.left, a);
      if (diff_h_by_2(x.right,x.left)) {
        tmp = x.right;
        //assert tmp'!=null; //'
        assume tmp'=null or tmp'!=null;
        if (diff_h_by_1(x.right.right,x.right.left)) {
           x = rotate_left(x.left, x.right.left, x.right.right, x.val, x.right.val); // SRR
          return x;
        } else if (eq_h(x.right.left,x.right.right)) {
          x = rotate_left(x.left, x.right.left, x.right.right, x.val, x.right.val); // SRR
          return x;
        } else {
          tmp = x.right.left;
          //assert tmp'!=null; //'
          assume tmp'=null or tmp'!=null;
          tmp = rotate_double_left(x.left, x.right.left.left, x.right.left.right, x.right.right, x.val, x.right.left.val, x.right.val); // DRR
          return tmp;
        }
      } else {
        x.height = get_max_height_add1(x.left, x.right) ;
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
  assume tmp'=null or tmp'!=null;
  dprint;
  tmp=insert(tmp, 11);
  assume false;
  assume tmp'=null or tmp'!=null;
  tmp=insert(tmp, 5);
  assume tmp'=null or tmp'!=null;
  tmp=insert(tmp, 7);
  assume tmp'=null or tmp'!=null;
  tmp=insert(tmp, 9);
  assume tmp'=null or tmp'!=null;
  tmp=delete(tmp,3);
  assume tmp'=null or tmp'!=null;
  tmp=delete(tmp,7);
  assume tmp'=null or tmp'!=null;
  tmp=delete(tmp,9);
  assume tmp'=null or tmp'!=null;
  tmp=delete(tmp,11);
}

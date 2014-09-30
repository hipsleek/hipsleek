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
/*avl<m, n, S> == self = null & m = 0 & n = 0 & S = {}
  or self::node<v, n, p, q> * p::avl<m1, n1, S1> * q::avl<m2, n2, S2> 
  & m = 1+m1+m2 &
  -1<=n1-n2<=1  & n=1+max(n1,n2) &
// n <= n1 + 2 & n <= n2 + 2 & tmp=max(n1, n2) & n = tmp + 1 
  S = union(S1, S2, {v}) &
  forall (x : (x notin S1 | x <= v)) & forall (y : (y notin S2 | y >= v))
  inv m >= 0 & n >= 0;*/
  
avl<m, n, S> == case{
  self = null -> [] m = 0 & n = 0 & S = {};
  self !=null -> [] self::node<v, n, p, q> * p::avl<m1, n1, S1> * q::avl<m2, n2, S2> 
      & m = 1+m1+m2 & -1<=n1-n2<=1  & n=1+max(n1,n2) & S = union(S1, S2, {v}) &
      forall (x : (x notin S1 | x <= v)) & forall (y : (y notin S2 | y >= v));}
  inv m >= 0 & n >= 0;
  
  

/* function to return the height of an avl tree */
int height(node x)
  requires x::avl<m, n, S>
  ensures x::avl<m, n, S> & res = n;
{
  int tmpi;
  if (x == null)
    return 0;
  else
    return x.height;
}

/*  function to rotate left */
node rotate_left(node l, node rl, node rr, int v, int vr)
  requires l::avl<lm, ln, Sl> * rl::avl<rlm, rln, Srl> * rr::avl<rrm, ln+1, Srr>
  & forall (x : (x notin Sl | x <= v)) & forall (y : (y notin Srl | y >= v))
  & forall (z : (z notin Srl | z <= vr)) & forall (w : (w notin Srr | w >= vr))
  & v <= vr & rln >= ln & rln <= ln + 1
  ensures res::avl<lm+rlm+rrm+2, 2+rln, S> & S = union(Sl, Srl, Srr, {v,vr});
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
  requires ll::avl<llm, lln, Sll> * lr::avl<lrm, lrn, Slr> * r::avl<rm, lln - 1, Sr>
  & forall (x : (x notin Sll | x <= vl)) & forall (y : (y notin Slr | y >= vl))
  & forall (z : (z notin Slr | z <= v)) & forall (w : (w notin Sr | w >= v))
  & vl <= v & lrn <= lln & lln <= lrn + 1
  ensures res::avl<2 + llm + lrm + rm, 2 + lrn, S> & S = union(Sll,Slr,Sr,{vl,v});
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
    & forall (x : (x notin Sl | x <= v)) & forall (y : (y notin Srll | y >= v))
    & forall (z : (z notin Srll | z <= vrl)) & forall (w : (w notin Srlr | w >= vrl))
    & forall (xx : (xx notin Srlr | xx <= vr)) & forall (yy : (yy notin Srr | yy >= vr))
    & v <= vrl <= vr & an = max(bn, cn) & cn <= bn + 1 & bn <= cn + 1 // & -1 <= bn - cn <= 1
  ensures res::avl<3 + am + bm + cm + dm, an + 2, S> & S = union(Sl,Srll,Srlr,Srr,{v,vrl,vr});
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
  requires a::avl<am, an, Sll> * b::avl<bm, bn, Slrl> * c::avl<cm, cn, Slrr> * d::avl<dm, an, Sr>
    & forall (x : (x notin Sll | x <= vl)) & forall (y : (y notin Slrl | y >= vl))
    & forall (z : (z notin Slrl | z <= vlr)) & forall (w : (w notin Slrr | w >= vlr))
    & forall (xx : (xx notin Slrr | xx <= v)) & forall (yy : (yy notin Sr | yy >= v))
    & vl <= vlr <= v & an = max(bn, cn) & cn <= bn + 1 & bn <= cn + 1 // & -1 <= bn - cn <= 1
  ensures res::avl<3 + am + bm + cm + dm, 2 + an, S> & S = union(Sll,Slrl,Slrr,Sr,{vl,vlr,v});
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
  requires x::avl<m, n, S> & x != null
  ensures res::avl<m+1, nn, Sn> & n <= nn <= n+1 & Sn = union(S, {a});

node remove_min_add(node x, ref myint a)
  requires x::avl<m,n,S> * a::myint<vv> & x != null
  ensures res::avl<m,n,Sn> * a'::myint<r> & union(S, {vv}) = union(Sn, {r}) & r <= vv & //'
    forall (xx : (xx notin Sn | r <= xx));

node remove_max_add(node x, ref myint a)
  requires x::avl<m,n,S> * a::myint<vv> & x != null
  ensures res::avl<m,n,Sn> * a'::myint<r> & union(S, {vv}) = union(Sn, {r}) & r >= vv & //'
    forall (xx : (xx notin Sn | r >= xx));

/* function to delete the smallest element in an avl tree */
node remove_min(node x, ref myint a)
    requires x::avl<m, n, S> * a::myint<_> & x != null
    ensures res::avl<m - 1, nn, Sn> * a'::myint<r> & n-1 <= nn <= n & union(Sn, {r}) = S & forall (xx : (xx notin S | r <= xx)); //'
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

/* function to delete the top node in a an avl tree */
node delete_top(node x)
  requires x::node<v, n, p, q> * p::avl<m1, n1, S1> * q::avl<m2, n2, S2>
    & n <= n1 + 2 & n <= n2 + 2 & exists (tmps : tmps=max(n1, n2) & n = tmps + 1)
    & forall (xx : (xx notin S1 | xx <= v)) & forall (y : (y notin S2 | y >= v))
  ensures res::avl<m1+m2, nn, Sn> & Sn = union(S1, S2) & n <= nn + 1 & nn <= n;

/* function to delete a node in a an avl tree */
node delete(node x, int a)
  requires x::avl<m, n, S>
  ensures res::avl<mm, nn, Sn> & n <= nn + 1 & nn <= n & m <= mm + 1 & mm <= m & Sn subset S & forall (xx : (xx notin S | xx = a | xx in Sn));

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

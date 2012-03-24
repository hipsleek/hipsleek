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
avl<"m":m, "n":n, "S":S> == self = null & ["m":m = 0; "n": n = 0; "S": S = {}]
  or self::node<v, n, p, q> * p::avl<m1, n1, S1> * q::avl<m2, n2, S2> & [
  "m" : m = 1+m1+m2 ; 
  "n" : -1 <= n1 - n2 <= 1 & n = 1 + max(n1, n2) ;
  "S" : S = union(S1, S2, {v}) & forall (x : (x notin S1 | x <= v)) & forall (y : (y notin S2 | y >= v))]
  inv true & ["m" : m >= 0;
    "n" : n >= 0];

  // n <= n1 + 2 & n <= n2 + 2 & tmp=max(n1, n2) & n = tmp + 1 & 

/* function to return the height of an avl tree */
int height(node x)
  requires x::avl<m, n, S>
  ensures x::avl<m, n, S> & ["n" : res = n];

/*  function to rotate left */
node rotate_left(node l, node rl, node rr, int v, int vr)
  requires l::avl<lm, ln, Sl> * rl::avl<rlm, rln, Srl> * rr::avl<rrm, ln+1, Srr> & [
  "S" : forall (x : (x notin Sl | x <= v)) & forall (y : (y notin Srl | y >= v))
      & forall (z : (z notin Srl | z <= vr)) & forall (w : (w notin Srr | w >= vr)) & v <= vr;
  "n" : rln >= ln & rln <= ln + 1]
  ensures res::avl<nm, nn, S> &
   ["S" : S = union(Sl, Srl, Srr, {v,vr});
    "m" : nm = lm+rlm+rrm+2;
    "n" : nn = 2+rln];
{
  node tmp, tmp2;
  int h;
  dprint;
  h = height(rl) + 1;
  tmp = new node(v, h, l, rl);
  h = h + 1;
  tmp2 = new node(vr, h, tmp, rr);
  return tmp2;
}


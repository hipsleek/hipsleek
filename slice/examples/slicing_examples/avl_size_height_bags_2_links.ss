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
avl<m, n, S, s> == case {
  self = null -> [] m = 0 & n = 0 & S = {} & s = 0;
  self !=null -> [] self::node<v, n, p, q> * p::avl<m1, n1, S1, s1> * q::avl<m2, n2, S2, s2>
	  & v >= 0
      & m = 1+m1+m2
	  & -1<=n1-n2<=1  & n=1+max(n1,n2)
	  & s = s1 + s2 + v
	  & S = union(S1, S2, {v}) &
      forall (x : (x notin S1 | x <= v)) & forall (y : (y notin S2 | y >= v));}
  inv m >= 0 & n >= 0 & ($ m >= n) & forall (z : (z notin S | z >= 0)) & s >= 0;

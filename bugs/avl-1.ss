/* representation of a node in an avl tree */
data node {
int val;
int height;
node left;
node right;
}

/* view for avl trees */
avl2<n, S> == self = null & S = {} & n = 0
 or (exists n3,tmp: self::node<v, n, p, q> * p::avl2<n1, S1> * q::avl2<n2, S2> & S =
union(S1, S2, {v})
 & forall (a: (a notin S1 | a <= v)) & forall (a: (a notin S2 | a >= v))
 & n3 = max(n1-n2, n2-n1) & n3 <= 1 & tmp = max(n1, n2) & n = tmp + 1)
inv n >= 0;

int find_min(node x)
 requires x::avl2<n, S> & x != null
 ensures x::avl2<n, S>  & x != null & forall (a: (a notin S | res <= a));
{
 if (x.left == null)
 return x.val;
 else
 return find_min(x.left);
}

/*
main(..)

  t = ...three nodes ..
  h = find_min(t);
  // t:;: ..three nodes..
  // t::avl<2,{a,b,c}>.

    l1,l2 |- F(l)
    p1,p2 |- F(p)
 ----------------------------------------
   l1,l2 ...p1,p2... |- F(l) & P(p)

 UNSAT(P1) \/ UNSAT(P2)
------------ -----------
 UNSAT(P1 & P2 ...)
    .
*/

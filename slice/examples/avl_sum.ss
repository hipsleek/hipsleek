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
/*
/*
// Example of independent properties
// Within each partitions of LHS must consider the dependent variables to minimize the
// size of entailment

Independent groups of dependent variables:
	"m":{m, m1, m2},
	"n":{n, n1, n2},
	"s":{s, s1, s2},
	"B":{B, B1, B2},
	"L":{L, L1, L2},
	"heap":{self, p, q}
-> need to consider the level of dependences of variables in a group.

Intermediate variables: {v} -> must be isolated to others when doing partitioning

// Choose relevant inductive hypotheses

avl<m, n, s, B, L> ==
  ["heap" : self = null;
   "m"    : m = 0;
   "n"    : n = 0;
   "s"    : s = 0;
   "B"    : B = {}
   "L"    : L = []
  ] or
  v >= 0 &
  ["heap" : self::node<v, p, q> * p::avl<m1, n1, s1, B1, L1> * q::avl<m2, n2, s2, B2, L2>;
   "m"    : m = 1+m1+m2;
            (P_m): m1 >= 0 & m2 >= 0;
			(P_mB): m1 = |B1| & m2 = |B2|
   "n"    : -1<=n1-n2<=1 & n=1+max(n1,n2);
            (P_n): n1 >= 0 & n2 >= 0
   "s"    : s = s1 + s2 + v & /*v >= 0; //duplicate v >= 0*/
            (P_s): s1 >= 0 & s2 >= 0 
   "B"    : B = union(B1, B2, {v}) & /*v >= 0*/ &
            forall (x : (x notin B1 | x <= v)) & forall (y : (y notin B2 | y >= v));
			(P_B): forall (z1 : (z1 notin B1 | z1 >= 0)) & forall (z2 : (z2 notin B2 | z2 >= 0));
			(P_mB): m1 = |B1| & m2 = |B2|;
			(P_LB): B1 = bag(L1) & B2 = bag(L2);
   "L"    : L = L1:::v:::L2
            (P_L): forall (t1 : (t1 notin L1 | t1 >= 0)) & forall (t2 : (t2 notin L2 | t2 >= 0));
		    (P_LB): B1 = bag(L1) & B2 = bag(L2);
  ]
  inv true & ["m"  : m >= 0;
			  "n"  : n >= 0;
			  "s"  : s >= 0;
			  "B"  : forall (z : (z notin B | z >= 0)); closure(B)$"B" = {B, B1$"P_B", B2$"P_B", v}
              "L"  : forall (t : (t notin L | t >= 0));
              "mB" : m = |B|; closure(m, B)$"mB" = {m, m1$"P_mB", m2$"P_mB", B, B1$"P_mB", B2$"P_mB"} does not include v because m and B are not related by v
              "LB" : B = bag(L); closure(L, B)$"LB" = {L, L1$"P_LB", L2$"P_LB", B, B1$"P_mB", B2$"P_mB"} does not include v>=0 because the RHS is bag constraint, not arith constraint 
			 ];

avl<m, n, s, B, L>
+ without any extra annotations, the properties of the data structure are independent.
  -> ignoring the linking edges of those independent properties.
+ linking (intermediate) variables can be detected automatically via graph algorithms (min-cut)
  * Type 1: symbol graph (Automatic Decomposition of Logical Theories)
  - Type 2: variables are defined as edges (Partitioning Methods for Satisfiability Testing on Large Formulas)

avl<m, n, s, B, b> ==
  ["heap" : self = null;
   "m"    : m = 0;
   "n"    : n = 0;
   "s"    : s = 0;
   "B"    : B = {}] or
  ["heap" : self::node<v, n, p, q> * p::avl<m1, n1, s1, B1> * q::avl<m2, n2, s2, B2>;
   "m"    : m = 1+m1+m2; (P1): m1 >= 0 & m2 >= 0; (P2): m1 = |B1| & m2 = |B2|
   "n"    : n=1+max(n1,n2); (P): n1 >= 0 & n2 >= 0
   "s"    : s = s1 + s2 + v & v >= 0; (P): s1 >= 0 & s2 >= 0 //duplicate v >= 0
   "B"    : B = union(B1, B2, {v}) & v >= 0
            forall (x : (x notin B1 | x <= v)) & forall (y : (y notin B2 | y >= v))
			(P1): forall (z1 : (z1 notin B1 | z1 >= 0)) &
                  forall (z2 : (z2 notin B2 | z2 >= 0))
			(P2): m1 = |B1| & m2 = |B2|

			case {
				n1 = n2 -> b = 0;
				n1 = n2 + 1 -> b = 1;
				n1 + 1 = n2 -> b = -1;
			}
  ]
  inv true & ["m" : m >= 0; "n" : n >= 0; "s" : s >= 0; "B" : forall (z : (z notin B | z >= 0)); "mB" : m = |B|];
			  
*/

avl<m, n, s, B> "$": {v} ==
  self = null & m = 0 & n = 0 & s = 0 & B = {}
  or self::node<v, n, p, q> * p::avl<m1, n1, s1, B1> * q::avl<m2, n2, s2, B2> &
  m = 1+m1+m2 &
  -1<=n1-n2<=1  & n=1+max(n1,n2) &
  /*"$"*/ v >= 0 &
  s = s1 + s2 + v &
  B = union(B1, B2, {v}) &
  forall (x : (x notin B1 | x <= v)) & forall (y : (y notin B2 | y >= v))
  inv m >= 0 & n >= 0 & s >= 0 & forall (z : (z notin B | z >= 0));
*/
/*
avl<m, n, s, B> ==
  self = null & ["m": m = 0; "n" : n = 0; "s" : s = 0; "B" : B = {}]
  or self::node<v, n, p, q> * p::avl<m1, n1, s1, B1> * q::avl<m2, n2, s2, B2> &
  v >= 0 &
  [
  "m" : m = 1+m1+m2;
  "n" : -1<=n1-n2<=1 & n=1+max(n1,n2);
  "s" : s = s1 + s2 + v;
  "B" : B = union(B1, B2, {v}) &
        forall (x : (x notin B1 | x <= v)) & forall (y : (y notin B2 | y >= v))
  ]
  inv true & ["m" : m >= 0; "n" : n >= 0; "s" : s >= 0; "B" : forall (z : (z notin B | z >= 0))];
*/

avl<m, n, B> ==
  self = null & m = 0 & n = 0 & B = {}
  or self::node<v, n, p, q> * p::avl<m1, n1, B1> * q::avl<m2, n2, B2> &
  m = 1+m1+m2 &
  -1<=n1-n2<=1  & n=1+max(n1,n2) &
  v >= 0 &
  B = union(B1, B2, {v}) &
  forall (x : (x notin B1 | x <= v)) & forall (y : (y notin B2 | y >= v))
  inv m >= 0 & n >= 0 & forall (z : (z notin B | z >= 0));

/*
avl<m, n, s> ==
  self = null & m = 0 & n = 0 & s = 0 or
  self::node<v, n, p, q> * p::avl<m1, n1, s1> * q::avl<m2, n2, s2> &
  m = 1+m1+m2 &
  -1<=n1-n2<=1  & n=1+max(n1,n2) &
  v >= 0 &
  s = s1 + s2 + v
  inv m >= 0 & n >= 0 & s >= 0;
*/

/* Just need the information about n */
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


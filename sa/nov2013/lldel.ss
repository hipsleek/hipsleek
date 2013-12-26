data node{
  int val;
  node next;
}


pred_extn size[R]<k> ==
   k=0 // base case
   or R::size<i> & k=1+i // recursive case
  inv k>=0;


ll<> == self = null or self::node<_, q> * q::ll<>;
lls<n> == self = null & n=0 or self::node<_, q> * q::lls<n-1>;

ltwo<p:node> == p=self & self = null  
   or self::node<_, q> * p::node<_,r> * q::ltwo<r>;
lthree<p:node,r:node> == p=r &r=null & self = null  
   or self::node<_, q1> * p::node<_,q2> * r::node<_,q3> * q1::lthree<q2,q3>;

HeapPred H(node a).
PostPred G(node a).
  relation P(int a, int b).
  relation Q(int a, int b, int c).
void delete (node x, int n)
 infer [G]  requires x::ll<>  ensures  G(x);
// infer [P,G]  requires x::lls<m> & P(m,n)  ensures  G(x);
//  infer [H,G]  requires H(x)  ensures  G(x);
//  infer [P,Q]  requires x::ll<n>*y::ll<m> & P(m,n)  ensures res::ll<k>*x::ll<n>*y::ll<m> & Q(m,n,k);
// requires x::lls<m> & m=n  ensures x::lls<m>;
{
  if (n ==0) return;
  else delete (x.next, n-1);
}

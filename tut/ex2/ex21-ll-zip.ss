data node {
  int val;
  node next;
}

ll<n> == emp & self=null & n=0
  or self::node<_,q>*q::ll<n-1>
  inv n>=0;

relation P(int n).
  relation Q(int n, int m, int r).

node zip(node x, node y)
  infer [P,Q]
  requires x::ll<n> * y::ll<m> & P(n,m)
  ensures res::ll<r> & Q(n,m,r);
{
  if (x==null) return null;
  else return new node(x.val+y.val,zip(x.next,y.next));
}

/*
# ex21-11-zip.ss

Need to simplify pure part of pre/post..
Expect:

  {[n,m]: n <= m}

Post Inference result:
zip$node~node
 EBase exists (Expl)[](Impl)[n; m](ex)[]x::ll{}<n> * y::ll{}<m>&((m!=0 | 
       1>n)) & n<=m & MayLoop[]&{FLOW,(4,5)=__norm#E}[]
         EAssume 
           (exists r_1397: res::ll{}<r_1397>&0<=n & 0<=m & n=r_1397 & 
           r_1397<=m&{FLOW,(4,5)=__norm#E})[]


*/

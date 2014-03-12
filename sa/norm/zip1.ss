data node{
  int val;
  node next;
}


pred_extn size[R]<k> ==
   k=0 // base case
   or R::size<i> & k=1+i // recursive case
  inv k>=0;


ll<n> == self = null & n=0  or self::node<_, q> * q::ll<n-1>
  inv n>=0;

ltwo<p:node> == p=self & self = null  
   or self::node<_, q> * p::node<_,r> * q::ltwo<r>;
lthree<p:node,r:node> == p=r &r=null & self = null  
   or self::node<_, q1> * p::node<_,q2> * r::node<_,q3> * q1::lthree<q2,q3>;

HeapPred H(node a, node b).
PostPred G(node a, node b, node c).
  relation P(int a, int b).
  relation Q(int a, int b, int c).
node zip (node x, node y)
//  infer [H,G]  requires H(x,y)  ensures  G(x,y,res);
//  infer [P,Q]  requires x::ll<n>*y::ll<m> & P(m,n)  ensures res::ll<k>*x::ll<n>*y::ll<m> & Q(m,n,k);

  requires x::ll<n> * y::ll<m>
 case {
   n!=m -> ensures true & flow __Error;
   n=m -> ensures x::ll<k> * y::ll<m> & res=x & k=n;
}

/*
requires x::ll<n> * y::ll<m> &  n=m
  ensures x::ll<k> * y::ll<m> & res=x & k=n;
*/
{
  if (x==null) 
    {
      if (y==null) return x;
      else 
        {
          //dprint;
          assert false assume false;
          //dprint;
          return x;
        }
    }
  else {
    // dprint;
    x.val = x.val+y.val;
    x.next = zip(x.next,y.next);
    return x;
  }
}

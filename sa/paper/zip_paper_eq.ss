data node{
	int val;
	node next;
}

ll<n> == self = null & n=0  or self::node<_, q> * q::ll<n-1>;

ltwo<p:node> == p=self & self = null  
   or self::node<_, q> * p::node<_,r> * q::ltwo<r>;
lthree<p:node,r:node> == p=r &r=null & self = null  
   or self::node<_, q1> * p::node<_,q2> * r::node<_,q3> * q1::lthree<q2,q3>;

HeapPred H(node a, node b).
PostPred G(node a, node b, node c).
  relation P(int a, int b).
  relation Q(int a, int b, int c).
node zip (node x, node y)
infer [H,G]  requires H(x,y)  ensures  G(x,y,res);
//  infer [P,Q]  requires x::ll<n>*y::ll<m> & P(m,n)  ensures res::ll<k>*x::ll<n>*y::ll<m> & Q(m,n,k);
//requires x::ltwo<y>  ensures x::lthree<y,res>;
{
  if (x==null) 
    {
      if (y==null) return x;
      else 
        {
          assume false;
          return x;
        }
    }
  else {
    return new node(x.val+y.val, zip(x.next,y.next));
  }
}

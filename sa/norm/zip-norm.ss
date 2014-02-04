data node{
	int val;
	node next;
}

ll<n> == self = null & n=0  or self::node<_, q> * q::ll<n-1>
inv n>=0;

  relation P(int a, int b).
  relation Q(int a, int b, int c).


node zip (node x, node y)
    infer [P,Q]  
requires x::ll<n>@L*y::ll<m>@L & P(m,n) 
ensures res::ll<k> & Q(n,m,k);
/*
requires x::ll<n>@L*y::ll<m>@L & n<=m 
ensures res::ll<k> & k<=m & k<=n;
*/
{
  if (x==null) return null;
  else {
    if (y==null) return null;
    else
    return new node(x.val+y.val, zip(x.next,y.next));
  }
}


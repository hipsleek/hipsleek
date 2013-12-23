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
  if (x==null) {
    if (y==null) return null;
    else return null;
  } else {
    if (y==null) return null;
    else
    return new node(x.val+y.val, zip(x.next,y.next));
  }
}

/*
# zip-2-norm
This result is weaker from fixcalc than zip-norm.ss

!!REL POST :  Q(n,m,k)
!!!POST:  (k=n | (k=m & k<=n))
!!!REL PRE :  P(m,n)
!!!PRE :  true

RELDEFN Q: ( n=0 & m=0 & k=0 & P(m,n)) -->  Q(n,m,k),
RELDEFN Q: ( n=0 & k=0 & 1<=m & P(m,n)) -->  Q(n,m,k),
RELDEFN Q: ( m=0 & k=0 & 1<=n & P(m,n)) -->  Q(n,m,k),
RELDEFN Q: ( Q(n_1039,m_1040,k_1064) & 0<=k_1064 & n_1039=n-1 & m_1040=m-1 & k=k_1064+
1 & 1<=m & 1<=n & P(m,n)) -->  Q(n,m,k)]


# zip-norm.ss

!!!REL POST :  Q(n,m,k)
!!!POST:  ((k=n & k<=m) | (k=m & k<n))

RELDEFN Q: ( n=0 & k=0 & 0<=m & P(m,n)) -->  Q(n,m,k),
RELDEFN Q: ( m=0 & k=0 & 1<=n & P(m,n)) -->  Q(n,m,k),
RELDEFN Q: ( Q(n_998,m_999,k_1020) & 0<=k_1020 & n_998=n-1 & m_999=m-1 & k=k_1020+1 & 
1<=m & 1<=n & P(m,n)) -->  Q(n,m,k)]


*/

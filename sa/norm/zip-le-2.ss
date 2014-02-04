data node{
	int val;
	node next;
}

ll<n> == self = null & n=0  or self::node<_, q> * q::ll<n-1>
inv n>=0;

  relation P(int a, int b).
  relation Q(int a, int b, int c).


node zip (node x, node y)
infer [P]  
requires x::ll<n>@L*y::ll<m>@L & P(m,n) 
ensures res::ll<k> ;
/*
requires x::ll<n>@L*y::ll<m>@L & n<=m 
ensures res::ll<k> & k=m;
*/
{
  if (x==null) return null;
  else {
    /* if (y==null) {  */
    /*    assert false assume false; */
    /*    return y; */
    /* } else     */
    return new node(x.val+y.val, zip(x.next,y.next));
  }
}

/*

Missing relational assumption?

[RELDEFN P: ( P(m,n) & 1<=m & 1<=n & n_1027=n-1 & m_1028=m-1) -->  P(m_1028,n_1027),
RELASS [P]: ( P(m,n)) -->  (m!=0 | 1>n),
RELDEFN Q: ( n=0 & m=0 & k=0 & P(m,n)) -->  Q(m,n,k),
RELDEFN Q: ( n=0 & k=0 & 1<=m & P(m,n)) -->  Q(m,n,k),
RELDEFN Q: ( Q(m_1028,n_1027,k_1049) & 0<=k_1049 & n_1027=n-1 & m_1028=m-1 & k=k_1049+
1 & 1<=m & 1<=n & P(m,n)) -->  Q(m,n,k)]

*/

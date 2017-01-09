data node {
  int val;
  node next;
}

/*
ll<n> == emp & self=null & n=0
  or self::node<_,q>*q::ll<n-1>
  inv n>=0;
*/

relation P(int n, int m).
  relation Q(int n, int m, int r).

HeapPred PP(node x, node@NI y).
PostPred QQ(node x, node y).

ll<n> == emp & self=null & n=0 
  or self::node<_,q>*q::ll<n-1>
  inv n>=0;



void append(node x, node y)
/*
  requires x::ll<n> * y::ll<m> & n>0
  ensures x::ll<n+m>;

  requires x::ls_nt<null> * y::node<_,_>@L & x!=null
  ensures x::ls_nt<y>;

  requires x::ls_nt<null> & x!=null
  ensures x::ls_nt<y>;

  infer [PP,QQ]
  requires PP(x,y)  ensures QQ(x,y);

*/
  infer [P,Q]
  requires x::ll<n>*y::ll<m> & P(n,m)
  ensures x::ll<r> & Q(n,m,r);
{
  if (x.next==null) x.next=y;
  else append(x.next,y);
}

/*
# ex23-11-app-size.ss  

[RELDEFN P: ( P(n,m_1425) & n=1+n_1424 & 1<=n_1424 & 0<=m_1425) -->  P(n_1424,m_1425),
RELASS [P]: ( P(n,m)) -->  (n!=0 | 0>m),
RELDEFN Q: ( n=1 & m=r_1386-1 & 1<=r_1386 & P(n,m)) -->  Q(n,m,r_1386),
RELDEFN Q: ( Q(n_1424,m,r_1440) & 0<=n_1424 & 1<=r_1440 & 0<=m & n=1+n_1424 & r_1386=1+
r_1440 & P(n,m)) -->  Q(n,m,r_1386)]

!!!  Q(n,m,r_1386) = ( Q(n_1424,m,r_1440) & 0<=n_1424 & 1<=r_1440 & 0<=m & n=1+n_1424 & r_1386=1+
r_1440) \/ ( n=1 & m=r_1386-1 & 1<=r_1386)
!!! bottom up
!!! fixcalc file name: fixcalc1.inf
!!! bottom_up_fp:[( Q(n,m,r_1386), n=r_1386-m & m<r_1386)]
!!! fixpoint:[( Q(n,m,r_1386), n=r_1386-m & m<r_1386, P(n,m), 1<=n)]
!!! REL POST :  Q(n,m,r_1386)
!!! POST:  n=r_1386-m & m<r_1386
!!! REL PRE :  P(n,m)
!!! PRE :  1<=n

*/

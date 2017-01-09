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



*/

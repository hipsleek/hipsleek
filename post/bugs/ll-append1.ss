data node {
  int val;
  node next;
}

ll<n> == self=null & n=0
  or self::node<_,q> * q::ll<n-1>
  inv n>=0;

void append(node x, node y)
  infer [@pre_n,@post_n]
  requires x::ll<n> * y::ll<m>
  ensures x::ll<r>;
{
  if (x.next == null)
    x.next=y;
  else
    append(x.next,y);
}

/*

*************************************
*******pure relation assumption ******
*************************************
[RELDEFN pre_1243: ( pre_1243(r_1226,n,m_1276) & 2<=n & n_1275=n-1 & 0<=m_1276) -->  pre_1243(r_1274,n_1275,m_1276),
RELASS [pre_1243]: ( pre_1243(r_1226,n,m)) -->  (n!=0 | 0>m),
RELDEFN post_1244: ( n=1 & r_1226=m+1 & 0<=m & pre_1243(r_1226,n,m)) -->  post_1244(r_1226,n,m),
RELDEFN post_1244: ( post_1244(r_1293,n_1275,m) & 0<=m & 0<=n_1275 & n=n_1275+1 & r_1293=r_1226-
1 & 2<=r_1226 & pre_1243(r_1226,n,m)) -->  post_1244(r_1226,n,m)]
*************************************

*************************************
*******fixcalc of pure relation *******
*************************************
[( post_1244(r_1226,n,m), n=r_1226-m & m<r_1226, true, true)]
*************************************

!!! REL POST :  post_1244(r_1226,n,m)
!!! POST:  n=r_1226-m & m<r_1226
!!! REL PRE :  true
!!! PRE :  true
Post Inference result:
append$node~node
 requires x::ll<n> * y::ll<m> & ((n!=0 | 0>m)) & ((n!=0 | 0>m)) & ((n!=0 | 0>m)) & ((n!=0 | 0>m)) & ((n!=0 | 0>m)) & ((n!=0 | 0>m)) & ((n!=0 | 0>m)) & ((n!=0 | 0>m)) & MayLoop[]
     ensures x::ll<r_1226> & 0<=n & 0<=m & n=r_1226-m & m<r_1226;

*/

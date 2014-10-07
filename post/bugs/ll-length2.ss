data node {
  int val;
  node next;
}

ll<n> == self=null & n=0
  or self::node<_,q> * q::ll<n-1>
  inv n>=0;

int length(node x)
  infer [@pre_n,@post_n]
  requires x::ll<n>
  ensures x::ll<m>;
{
  if (x == null)
    return 0;
  else
    return 1+length(x.next);
}

/*

Why don't have pre?

*************************************
*******pure relation assumption ******
*************************************
[RELDEFN pre_1240: ( 2<=n & pre_1240(m_1239,n) & n_1264=n-1) -->  pre_1240(m_1263,n_1264),
RELDEFN pre_1240: ( n_1264=0) -->  pre_1240(m_1263,n_1264),
RELDEFN post_1241: ( res=0 & n=0 & m_1239=0 & pre_1240(m_1239,n)) -->  post_1241(m_1239,n,res),
RELDEFN post_1241: ( post_1241(m_1276,n_1264,v_int_18_1281) & 0<=m_1276 & res=v_int_18_1281+1 & n_1264=n-1 & m_1239=m_1276+1 & 1<=n & pre_1240(m_1239,n)) -->  post_1241(m_1239,n,res)]
*************************************

*************************************
*******fixcalc of pure relation *******
*************************************
[( post_1241(m_1239,n,res), m_1239=res & n=res, true, true)]
*************************************

!!! REL POST :  post_1241(m_1239,n,res)
!!! POST:  m_1239=res & n=res
!!! REL PRE :  true
!!! PRE :  true
Post Inference result:
length$node
 requires x::ll<n> & MayLoop[]
     ensures x::ll<m_1239> & 0<=n & m_1239=res & n=res;

*/

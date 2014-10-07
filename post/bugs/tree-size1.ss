data node {
  int val;
  node left;
  node right;
}

tree<size> == self=null & size=0
  or self::node<_,l,r> * l::tree<size1> * r::tree<size2> & size=size1+size2+1
  inv size>=0;

int size(node x)
  infer [@pre_n,@post_n]
  requires x::tree<n>
  ensures x::tree<m>;
{
  if (x==null) return 0;
  else return size(x.left) + size(x.right) + 1;
}

/*

Why don't have pre?

*************************************
*******pure relation assumption ******
*************************************
[RELDEFN pre_1253: ( pre_1253(m_1236,n) & 1<=n_1282 & n_1282<n) -->  pre_1253(m_1281,n_1282),
RELDEFN pre_1253: ( n_1282=0) -->  pre_1253(m_1281,n_1282),
RELDEFN pre_1253: ( 0<=m_1293 & n_1282<=(n-2) & 0<=n_1282 & pre_1253(m_1236,n) &
post_1254(m_1293,n_1282,v_int_19_1230') & n_1297=(n-n_1282)-1) -->  pre_1253(m_1296,n_1297),
RELDEFN pre_1253: ( n_1297=0) -->  pre_1253(m_1296,n_1297),
RELDEFN post_1254: ( res=0 & n=0 & m_1236=0 & pre_1253(m_1236,n)) -->  post_1254(m_1236,n,res),
RELDEFN post_1254: ( post_1254(m_1310,n_1297,v_int_19_1318) &
post_1254(m_1293,n_1282,v_int_19_1317) & 0<=n_1282 & 0<=n_1297 & 0<=m_1310 &
0<=m_1293 & v_int_19_1318=(res-v_int_19_1317)-1 & n=n_1282+n_1297+1 &
m_1236=m_1310+m_1293+1 & pre_1253(m_1236,n)) -->  post_1254(m_1236,n,res)]
*************************************

*************************************
*******fixcalc of pure relation *******
*************************************
[( post_1254(m_1236,n,res), m_1236=res & n=res, true, true)]
*************************************

!!! REL POST :  post_1254(m_1236,n,res)
!!! POST:  m_1236=res & n=res
!!! REL PRE :  true
!!! PRE :  true
Post Inference result:
size$node
 requires x::tree<n> & MayLoop[]
     ensures x::tree<m_1236> & 0<=n & m_1236=res & n=res;

*/

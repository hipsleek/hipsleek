data node {
  int val;
  node left;
  node right;
}

tree<height> == self=null & height=0
  or self::node<_,l,r> * l::tree<height1> * r::tree<height2> & height=max(height1,height2)+1
  inv height>=0;

int height(node x)
  infer [@pre_n,@post_n]
  requires x::tree<n>
  ensures x::tree<m>;
{
  if (x==null) return 0;
  else if (height(x.left) > height(x.right))
    return height(x.left) + 1;
  else
    return height(x.right) + 1;
}

/*

Why don't we have pre?

*************************************
*******pure relation assumption ******
*************************************
[RELDEFN pre_1265: ( pre_1265(m_1256,n) & 1<=n_1295 & n_1295<n) -->  pre_1265(m_1294,n_1295),
RELDEFN pre_1265: ( n_1295=0) -->  pre_1265(m_1294,n_1295),
RELDEFN pre_1265: ( 0<=m_1310 & post_1266(m_1310,n_1295,v_int_17_1230') & n_1295=n-1 &
pre_1265(m_1256,n) & 1<=n_1314 & n_1314<n) -->  pre_1265(m_1313,n_1314),
RELDEFN pre_1265: ( 0<=m_1310 & post_1266(m_1310,n_1295,v_int_17_1230') & 0<=n_1295 &
n_1295<=(n-2) & pre_1265(m_1256,n) & n_1314=n-1) -->  pre_1265(m_1313,n_1314),
RELDEFN pre_1265: ( n_1314=0) -->  pre_1265(m_1313,n_1314),
RELDEFN pre_1265: ( 0<=m_1330 & post_1266(m_1330,n_1314,v_int_17_1340) & pre_1265(m_1256,n) &
0<=n_1314 & v_int_17_1340<v_int_17_1339 & n_1314<n & n_1295=n-1 &
post_1266(n_1344,n_1295,v_int_17_1339) & 1<=n_1344) -->  pre_1265(m_1343,n_1344),
RELDEFN pre_1265: ( 0<=m_1330 & post_1266(m_1330,n_1314,v_int_17_1340) & pre_1265(m_1256,n) &
n_1314=n-1 & v_int_17_1340<v_int_17_1339 & n_1295<=(n-2) & 0<=n_1295 &
post_1266(n_1344,n_1295,v_int_17_1339) & 1<=n_1344) -->  pre_1265(m_1343,n_1344),
RELDEFN pre_1265: ( n_1344=0) -->  pre_1265(m_1343,n_1344),
RELDEFN pre_1265: ( 0<=m_1310 & post_1266(m_1310,n_1295,v_int_17_1369) & pre_1265(m_1256,n) &
n_1295=n-1 & v_int_17_1369<=v_int_17_1370 & n_1314<n & 0<=n_1314 &
post_1266(n_1374,n_1314,v_int_17_1370) & 1<=n_1374) -->  pre_1265(m_1373,n_1374),
RELDEFN pre_1265: ( 0<=m_1310 & post_1266(m_1310,n_1295,v_int_17_1369) & pre_1265(m_1256,n) &
0<=n_1295 & v_int_17_1369<=v_int_17_1370 & n_1295<=(n-2) & n_1314=n-1 &
post_1266(n_1374,n_1314,v_int_17_1370) & 1<=n_1374) -->  pre_1265(m_1373,n_1374),
RELDEFN pre_1265: ( n_1374=0) -->  pre_1265(m_1373,n_1374),
RELDEFN post_1266: ( res=0 & n=0 & m_1256=0 & pre_1265(m_1256,n)) -->  post_1266(m_1256,n,res),
RELDEFN post_1266: ( 0<=m_1310 & v_int_17_1340<v_int_17_1339 & m_1330<=m_1362 & 0<=m_1330 &
0<=n_1314 & post_1266(m_1310,n_1295,v_int_17_1339) &
post_1266(m_1330,n_1314,v_int_17_1340) &
post_1266(m_1362,m_1310,v_int_18_1400) & pre_1265(m_1256,n) &
res=v_int_18_1400+1 & n_1295=n-1 & m_1256=m_1362+1 & n_1314<n) -->  post_1266(m_1256,n,res),
RELDEFN post_1266: ( 0<=m_1310 & v_int_17_1340<v_int_17_1339 & m_1330<=m_1362 & 0<=m_1330 &
0<=n_1295 & post_1266(m_1310,n_1295,v_int_17_1339) &
post_1266(m_1330,n_1314,v_int_17_1340) &
post_1266(m_1362,m_1310,v_int_18_1400) & pre_1265(m_1256,n) &
res=v_int_18_1400+1 & n_1314=n-1 & m_1256=m_1362+1 & n_1295<=(n-2)) -->  post_1266(m_1256,n,res),
RELDEFN post_1266: ( 0<=m_1310 & v_int_17_1340<v_int_17_1339 & 0<=n_1314 & m_1362<m_1330 &
0<=m_1362 & post_1266(m_1310,n_1295,v_int_17_1339) &
post_1266(m_1330,n_1314,v_int_17_1340) &
post_1266(m_1362,m_1310,v_int_18_1400) & pre_1265(m_1256,n) &
res=v_int_18_1400+1 & n_1295=n-1 & m_1256=m_1330+1 & n_1314<n) -->  post_1266(m_1256,n,res),
RELDEFN post_1266: ( 0<=m_1310 & v_int_17_1340<v_int_17_1339 & 0<=n_1295 & m_1362<m_1330 &
0<=m_1362 & post_1266(m_1310,n_1295,v_int_17_1339) &
post_1266(m_1330,n_1314,v_int_17_1340) &
post_1266(m_1362,m_1310,v_int_18_1400) & pre_1265(m_1256,n) &
res=v_int_18_1400+1 & n_1314=n-1 & m_1256=m_1330+1 & n_1295<=(n-2)) -->  post_1266(m_1256,n,res),
RELDEFN post_1266: ( 0<=m_1331 & v_int_17_1369<=v_int_17_1370 & m_1392<=m_1310 & 0<=m_1392 &
0<=n_1314 & post_1266(m_1310,n_1295,v_int_17_1369) &
post_1266(m_1331,n_1314,v_int_17_1370) &
post_1266(m_1392,m_1331,v_int_20_1429) & pre_1265(m_1256,n) &
res=v_int_20_1429+1 & n_1295=n-1 & m_1256=m_1310+1 & n_1314<n) -->  post_1266(m_1256,n,res),
RELDEFN post_1266: ( 0<=m_1331 & v_int_17_1369<=v_int_17_1370 & m_1392<=m_1310 & 0<=m_1392 &
0<=n_1295 & post_1266(m_1310,n_1295,v_int_17_1369) &
post_1266(m_1331,n_1314,v_int_17_1370) &
post_1266(m_1392,m_1331,v_int_20_1429) & pre_1265(m_1256,n) &
res=v_int_20_1429+1 & n_1314=n-1 & m_1256=m_1310+1 & n_1295<=(n-2)) -->  post_1266(m_1256,n,res),
RELDEFN post_1266: ( 0<=m_1331 & v_int_17_1369<=v_int_17_1370 & 0<=n_1314 & m_1310<m_1392 &
0<=m_1310 & post_1266(m_1310,n_1295,v_int_17_1369) &
post_1266(m_1331,n_1314,v_int_17_1370) &
post_1266(m_1392,m_1331,v_int_20_1429) & pre_1265(m_1256,n) &
res=v_int_20_1429+1 & n_1295=n-1 & m_1256=m_1392+1 & n_1314<n) -->  post_1266(m_1256,n,res),
RELDEFN post_1266: ( 0<=m_1331 & v_int_17_1369<=v_int_17_1370 & 0<=n_1295 & m_1310<m_1392 &
0<=m_1310 & post_1266(m_1310,n_1295,v_int_17_1369) &
post_1266(m_1331,n_1314,v_int_17_1370) &
post_1266(m_1392,m_1331,v_int_20_1429) & pre_1265(m_1256,n) &
res=v_int_20_1429+1 & n_1314=n-1 & m_1256=m_1392+1 & n_1295<=(n-2)) -->  post_1266(m_1256,n,res)]
*************************************

*************************************
*******fixcalc of pure relation *******
*************************************
[( post_1266(m_1256,n,res), m_1256=res & n=res, true, true)]
*************************************

!!! REL POST :  post_1266(m_1256,n,res)
!!! POST:  m_1256=res & n=res
!!! REL PRE :  true
!!! PRE :  true
Post Inference result:
height$node
 requires x::tree<n> & MayLoop[]
     ensures x::tree<m_1256> & 0<=n & m_1256=res & n=res;

*/

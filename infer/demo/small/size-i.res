
!!! Full processing file "size-i.ss"
Parsing file "size-i.ss" by default parser...

!!!  processing primitives "["prelude.ss"]
Starting Omega...oc

Checking procedure append$node~node... 
*************************************
*******pure relation assumption ******
*************************************
[RELDEFN P1: ( P1(n,m_937) & 2<=n & n_936=n-1 & 0<=m_937) -->  P1(n_936,m_937),
RELDEFN Q1: ( n=1 & z=m+1 & 0<=m & P1(n,m)) -->  Q1(n,m,z),
RELDEFN Q1: ( Q1(n_936,m,z_955) & 0<=n_936 & n=n_936+1 & z_955=z-1 & 0<=m & 2<=z & P1(n,m)) -->  Q1(n,m,z)]
*************************************

*************************************
*******fixcalc of pure relation *******
*************************************
[( Q1(n,m,z), n=z-m & 0<=m & m<z, P1(n,m), true)]
*************************************

!!! REL POST :  Q1(n,m,z)
!!! POST:  n=z-m & 0<=m & m<z
!!! REL PRE :  P1(n,m)
!!! PRE :  true
Procedure append$node~node SUCCESS

Checking procedure copy$node... 
*************************************
*******pure relation assumption ******
*************************************
[RELDEFN P2: ( P2(n) & 1<=n & n_996=n-1) -->  P2(n_996),
RELDEFN Q2: ( Q2(n_996,m_1006) & 0<=m_1006 & n_996=n-1 & m=m_1006+1 & 1<=n & P2(n)) -->  Q2(n,m),
RELDEFN Q2: ( n=0 & m=0 & P2(n)) -->  Q2(n,m)]
*************************************

*************************************
*******fixcalc of pure relation *******
*************************************
[( Q2(n,m), m=n & 0<=n, P2(n), true)]
*************************************

!!! REL POST :  Q2(n,m)
!!! POST:  m=n & 0<=n
!!! REL PRE :  P2(n)
!!! PRE :  true
Procedure copy$node SUCCESS

Checking procedure del_index$node~int... 
*************************************
*******pure relation assumption ******
*************************************
[RELDEFN P1: ( 2<=i & 1<=n & P1(i,n) & v_int_76_834'=i-1 & n_1114=n-1) -->  P1(v_int_76_834',n_1114),
RELDEFN P1: ( 1<=n & i<=0 & P1(i,n) & v_int_76_834'=i-1 & n_1114=n-1) -->  P1(v_int_76_834',n_1114),
RELASS [P1]: ( P1(i,n)) -->  (n!=0 | 2>i) & (n!=0 | i>0),
RELASS [P1]: ( P1(i,n)) -->  n!=0 | i!=1,
RELASS [P1]: ( P1(i,n)) -->  n!=1 | i!=1,
RELDEFN Q1: ( i=1 & m=n-1 & 2<=n & P1(i,n)) -->  Q1(n,m,i),
RELDEFN Q1: ( 1<=v_int_76_1134 & 0<=m_1133 & Q1(n_1114,m_1133,v_int_76_1134) & P1(i,n) & 
n_1114=n-1 & i=v_int_76_1134+1 & m=m_1133+1 & 1<=n) -->  Q1(n,m,i),
RELDEFN Q1: ( 0<=m_1133 & v_int_76_1134<=(0-1) & Q1(n_1114,m_1133,v_int_76_1134) & 
P1(i,n) & n_1114=n-1 & i=v_int_76_1134+1 & m=m_1133+1 & 1<=n) -->  Q1(n,m,i)]
*************************************

*************************************
*******fixcalc of pure relation *******
*************************************
[( Q1(n,i,m), n=m+1 & 1<=i & i<=m, P1(i,n), 1<=i & i<n)]
*************************************

!!! REL POST :  Q1(n,i,m)
!!! POST:  n=m+1 & 1<=i & i<=m
!!! REL PRE :  P1(i,n)
!!! PRE :  1<=i & i<n
Procedure del_index$node~int SUCCESS

Checking procedure del_val$node~int... 
*************************************
*******pure relation assumption ******
*************************************
[RELDEFN P1: ( 1<=n & n_1193=n-1 & P1(n,a')) -->  P1(n_1193,a'),
RELDEFN Q1: ( n=0 & m=0 & P1(n,a)) -->  Q1(n,m,a),
RELDEFN Q1: ( m=n-1 & 1<=n & P1(n,a)) -->  Q1(n,m,a),
RELDEFN Q1: ( 0<=m_1205 & n_1193=n-1 & m=m_1205+1 & 1<=n & P1(n,a) & Q1(n_1193,m_1205,a)) -->  Q1(n,m,a)]
*************************************

*************************************
*******fixcalc of pure relation *******
*************************************
[( Q1(n,a,m), 0<=m & (n-1)<=m & m<=n, P1(n,a), true)]
*************************************

!!! REL POST :  Q1(n,a,m)
!!! POST:  0<=m & (n-1)<=m & m<=n
!!! REL PRE :  P1(n,a)
!!! PRE :  true
Procedure del_val$node~int SUCCESS

Checking procedure insert$node~int... 
*************************************
*******pure relation assumption ******
*************************************
[RELDEFN P2: ( P2(n) & n=n_1265+1 & 1<=n_1265) -->  P2(n_1265),
RELDEFN Q2: ( m=2 & n=1 & P2(n)) -->  Q2(n,m),
RELDEFN Q2: ( Q2(n_1265,m_1290) & 0<=n_1265 & n=n_1265+1 & m_1290=m-1 & 2<=m & P2(n)) -->  Q2(n,m)]
*************************************

*************************************
*******fixcalc of pure relation *******
*************************************
[( Q2(n,m), n=m-1 & 2<=m, P2(n), true)]
*************************************

!!! REL POST :  Q2(n,m)
!!! POST:  n=m-1 & 2<=m
!!! REL PRE :  P2(n)
!!! PRE :  true
Procedure insert$node~int SUCCESS

Checking procedure traverse$node... 
*************************************
*******pure relation assumption ******
*************************************
[RELDEFN P2: ( P2(n) & 1<=n & n_1332=n-1) -->  P2(n_1332),
RELDEFN Q2: ( Q2(n_1332,m_1338) & 0<=m_1338 & n_1332=n-1 & m=m_1338+1 & 1<=n & P2(n)) -->  Q2(n,m),
RELDEFN Q2: ( n=0 & m=0 & P2(n)) -->  Q2(n,m)]
*************************************

*************************************
*******fixcalc of pure relation *******
*************************************
[( Q2(n,m), m=n & 0<=n, P2(n), true)]
*************************************

!!! REL POST :  Q2(n,m)
!!! POST:  m=n & 0<=n
!!! REL PRE :  P2(n)
!!! PRE :  true
Procedure traverse$node SUCCESS

Termination checking result:

Stop Omega... 411 invocations 
0 false contexts at: ()

Total verification time: 1.46 second(s)
	Time spent in main process: 0.91 second(s)
	Time spent in child processes: 0.55 second(s)


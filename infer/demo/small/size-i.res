
!!! Full processing file "size-i.ss"
Parsing file "size-i.ss" by default parser...

!!!  processing primitives "["prelude.ss"]
Starting Omega...oc

Checking procedure append$node~node... 
*************************************
*******pure relation assumption ******
*************************************
[RELDEFN P1: ( P1(n,m_934) & 2<=n & n_933=n-1 & 0<=m_934) -->  P1(n_933,m_934),
RELDEFN Q1: ( n=1 & z=m+1 & 0<=m & P1(n,m)) -->  Q1(n,m,z),
RELDEFN Q1: ( Q1(n_933,m,z_952) & 0<=n_933 & n=n_933+1 & z_952=z-1 & 0<=m & 2<=z & P1(n,m)) -->  Q1(n,m,z)]
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
[RELDEFN P2: ( P2(n) & 1<=n & n_993=n-1) -->  P2(n_993),
RELDEFN Q2: ( Q2(n_993,m_1003) & 0<=m_1003 & n_993=n-1 & m=m_1003+1 & 1<=n & P2(n)) -->  Q2(n,m),
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
[RELDEFN P1: ( 2<=i & 1<=n & P1(i,n) & v_int_76_831'=i-1 & n_1104=n-1) -->  P1(v_int_76_831',n_1104),
RELDEFN P1: ( 1<=n & i<=0 & P1(i,n) & v_int_76_831'=i-1 & n_1104=n-1) -->  P1(v_int_76_831',n_1104),
RELASS [P1]: ( P1(i,n)) -->  (n!=0 | 2>i) & (n!=0 | i>0),
RELASS [P1]: ( P1(i,n)) -->  n!=0 | i!=1,
RELASS [P1]: ( P1(i,n)) -->  n!=1 | i!=1,
RELDEFN Q1: ( i=1 & m=n-1 & 2<=n & P1(i,n)) -->  Q1(n,m,i),
RELDEFN Q1: ( 1<=v_int_76_1124 & 0<=m_1123 & Q1(n_1104,m_1123,v_int_76_1124) & P1(i,n) & 
n_1104=n-1 & i=v_int_76_1124+1 & m=m_1123+1 & 1<=n) -->  Q1(n,m,i),
RELDEFN Q1: ( 0<=m_1123 & v_int_76_1124<=(0-1) & Q1(n_1104,m_1123,v_int_76_1124) & 
P1(i,n) & n_1104=n-1 & i=v_int_76_1124+1 & m=m_1123+1 & 1<=n) -->  Q1(n,m,i)]
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
[RELDEFN P1: ( 1<=n & n_1180=n-1 & P1(n,a')) -->  P1(n_1180,a'),
RELDEFN Q1: ( n=0 & m=0 & P1(n,a)) -->  Q1(n,m,a),
RELDEFN Q1: ( m=n-1 & 1<=n & P1(n,a)) -->  Q1(n,m,a),
RELDEFN Q1: ( 0<=m_1192 & n_1180=n-1 & m=m_1192+1 & 1<=n & P1(n,a) & Q1(n_1180,m_1192,a)) -->  Q1(n,m,a)]
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
[RELDEFN P2: ( P2(n) & n=n_1252+1 & 1<=n_1252) -->  P2(n_1252),
RELDEFN Q2: ( m=2 & n=1 & P2(n)) -->  Q2(n,m),
RELDEFN Q2: ( Q2(n_1252,m_1277) & 0<=n_1252 & n=n_1252+1 & m_1277=m-1 & 2<=m & P2(n)) -->  Q2(n,m)]
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
[RELDEFN P2: ( P2(n) & 1<=n & n_1319=n-1) -->  P2(n_1319),
RELDEFN Q2: ( Q2(n_1319,m_1325) & 0<=m_1325 & n_1319=n-1 & m=m_1325+1 & 1<=n & P2(n)) -->  Q2(n,m),
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

Stop Omega... 409 invocations 
0 false contexts at: ()

Total verification time: 1.46 second(s)
	Time spent in main process: 0.91 second(s)
	Time spent in child processes: 0.55 second(s)


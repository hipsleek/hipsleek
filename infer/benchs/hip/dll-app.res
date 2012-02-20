
Processing file "dll-app.ss"
Parsing dll-app.ss ...
Parsing ../../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure append$node2~node2... 
!!! REL :  C(t,m,n)
!!! POST:  n>=0 & t>=n & t=m+n
!!! PRE :  0<=n & 0<=m
!!! NEW RELS:[ (t=n & 0<=n & m=0) --> C(t,m,n),
 (exists(flted_12_644:(t=2 & t_611=1 | 2+flted_12_644=t & 1+t_611=t & 
  3<=t) & C(t_611,m_584,n_586) & 1<=m & 0<=n & n_586=n & 1+
  m_584=m)) --> C(t,m,n),
 (t_607=0 & 1+m_584=m & n_586=n & t=1 & 0<=n & 1<=m & 
  C(t_607,m_584,n_586)) --> C(t,m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append$node2~node2 SUCCESS

Termination checking result:

Stop Omega... 163 invocations 
0 false contexts at: ()

Total verification time: 0.58 second(s)
	Time spent in main process: 0.4 second(s)
	Time spent in child processes: 0.18 second(s)

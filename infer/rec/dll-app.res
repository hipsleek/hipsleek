
Processing file "dll-app.ss"
Parsing dll-app.ss ...
Parsing /home2/loris/hg/sl_infer/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure append$node2~node2... 
!!! REL :  C(t,m,n)
!!! POST:  n>=0 & t>=n & t=m+n
!!! PRE :  0<=n & 0<=m
!!! NEW RELS:[ (t=n & 0<=n & m=0) --> C(t,m,n),
 (exists(flted_12_683:(t=2 & t_650=1 | 2+flted_12_683=t & 1+t_650=t & 
  3<=t) & C(t_650,m_623,n_625) & 1<=m & 0<=n & n_625=n & 1+
  m_623=m)) --> C(t,m,n),
 (t_646=0 & 1+m_623=m & n_625=n & t=1 & 0<=n & 1<=m & 
  C(t_646,m_623,n_625)) --> C(t,m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append$node2~node2 SUCCESS

Checking procedure append2$node2~node2... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ m!=0, m!=0, m!=0]
!!! REL :  D(t,m,n,r,p,q)
!!! POST:  n>=0 & 1=m & q=r & n+1=t
!!! PRE :  m=1 & 0<=n
!!! NEW RELS:[ (m=1 & n=0 & r=q & t=1) --> D(t,m,n,r,p,q),
 (exists(flted_12_828:(t=2 & n=1 | 2+flted_12_828=t & 1+n=t & 3<=t) & r=q & 
  m=1)) --> D(t,m,n,r,p,q),
 (m=1 & n=0 & r=q & t=1) --> D(t,m,n,r,p,q)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append2$node2~node2 SUCCESS

Termination checking result:

Stop Omega... 327 invocations 
0 false contexts at: ()

Total verification time: 0.524032 second(s)
	Time spent in main process: 0.128008 second(s)
	Time spent in child processes: 0.396024 second(s)

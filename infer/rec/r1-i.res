
Processing file "r1-i.ss"
Parsing r1-i.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure append$node~node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ n!=0, n!=0]
!!! REL :  A(n,m,z)
!!! POST:  m>=0 & z>=(1+m) & z=n+m
!!! PRE :  0<=m & 1<=n
!!! NEW RELS:[ (1+m=z & 1<=z & n=1) --> A(n,m,z),
 (1<=z_609 & 1+n_586=n & m_587=m & -1+z=z_609 & 0<=m & 1<=n & 
  A(n_586,m_587,z_609)) --> A(n,m,z)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append$node~node SUCCESS

Checking procedure foo$node... 
!!! REL :  F(res,n)
!!! POST:  n>=0 & 0=res
!!! PRE :  0<=n
!!! NEW RELS:[ (n=0 & res=0) --> F(res,n),
 (exists(flted_7_643:(n_648=0 & n=1 | flted_7_643=n_648 & -1+n=n_648 & 
  1<=n_648) & F(m_29',n_648) & res=m_29')) --> F(res,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure foo$node SUCCESS

Checking procedure length$node... 
!!! REL :  R(res,n)
!!! POST:  res>=0 & res=n
!!! PRE :  0<=n
!!! NEW RELS:[ (n=0 & res=0) --> R(res,n),
 (exists(flted_7_678:(n_683=0 & n=1 | flted_7_678=n_683 & -1+n=n_683 & 
  1<=n_683) & R(r_30',n_683) & -1+res=r_30')) --> R(res,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure length$node SUCCESS

Termination checking result:

Stop Omega... 245 invocations 
0 false contexts at: ()

Total verification time: 0.4 second(s)
	Time spent in main process: 0.25 second(s)
	Time spent in child processes: 0.15 second(s)

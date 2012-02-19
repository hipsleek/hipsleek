
Processing file "cll-count2.ss"
Parsing cll-count2.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure count$node... 
!!! REL :  A(res,n)
!!! POST:  res>=0 & res=n
!!! PRE :  0<=n
!!! NEW RELS:[ (res=0 & n=0) --> A(res,n),
 (res=0 & n=0) --> A(res,n),
 (exists(n_585:res=1 & n=1 | -1+res=n_585 & -1+n=n_585 & 
  1<=n_585)) --> A(res,n),
 (res=0 & n=0) --> A(res,n),
 (n=1 & res=1) --> A(res,n),
 (n=1 & res=1) --> A(res,n),
 (n=1 & res=1) --> A(res,n),
 (n=1 & res=1) --> A(res,n),
 (n=1 & res=1) --> A(res,n),
 (n=1 & res=1) --> A(res,n),
 (n=1 & res=1) --> A(res,n),
 (n=1 & res=1) --> A(res,n),
 (n=1 & res=1) --> A(res,n),
 (n=1 & res=1) --> A(res,n),
 (n=1 & res=1) --> A(res,n),
 (n=1 & res=1) --> A(res,n),
 (n=1 & res=1) --> A(res,n),
 (n=1 & res=1) --> A(res,n),
 (n=1 & res=1) --> A(res,n),
 (n=1 & res=1) --> A(res,n),
 (n=1 & res=1) --> A(res,n),
 (n=1 & res=1) --> A(res,n),
 (n=1 & res=1) --> A(res,n),
 (n=1 & res=1) --> A(res,n),
 (n=1 & res=1) --> A(res,n),
 (n=1 & res=1) --> A(res,n),
 (n=1 & res=1) --> A(res,n),
 (res=0 & n=0) --> A(res,n),
 (n=1 & res=1) --> A(res,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure count$node SUCCESS

Termination checking result:

Stop Omega... 386 invocations 
0 false contexts at: ()

Total verification time: 1.45 second(s)
	Time spent in main process: 0.98 second(s)
	Time spent in child processes: 0.47 second(s)

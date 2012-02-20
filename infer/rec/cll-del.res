
Processing file "cll-del.ss"
Parsing cll-del.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure delete$node... 
!!! REL :  A(m,n)
!!! POST:  m>=0 & m+1=n
!!! PRE :  1<=n
!!! NEW RELS:[ (exists(flted_11_599:m=1 & n=2 | -1+n=m & 1+flted_11_599=m & 
  2<=m)) --> A(m,n),
 (n=1 & m=0) --> A(m,n),
 (m=1 & n=2) --> A(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete$node SUCCESS

Termination checking result:

Stop Omega... 147 invocations 
0 false contexts at: ()

Total verification time: 0.37 second(s)
	Time spent in main process: 0.19 second(s)
	Time spent in child processes: 0.18 second(s)

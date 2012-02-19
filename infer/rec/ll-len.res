
Processing file "ll-len.ss"
Parsing ll-len.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure length$node... 
!!! REL :  R(res,n)
!!! POST:  res>=0 & res=n
!!! PRE :  0<=n
!!! NEW RELS:[ (n=0 & res=0) --> R(res,n),
 (exists(flted_7_534:(n_539=0 & n=1 | flted_7_534=n_539 & -1+n=n_539 & 
  1<=n_539) & R(r_24',n_539) & -1+res=r_24')) --> R(res,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure length$node SUCCESS

Termination checking result:

Stop Omega... 94 invocations 
0 false contexts at: ()

Total verification time: 0.22 second(s)
	Time spent in main process: 0.16 second(s)
	Time spent in child processes: 0.06 second(s)

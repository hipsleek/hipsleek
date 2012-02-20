
Processing file "ll-len2.ss"
Parsing ll-len2.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure length$node... 
!!! REL :  R(n,res)
!!! POST:  n>=0 & n=res
!!! PRE :  0<=n
!!! NEW RELS:[ (n=0 & res=0) --> R(n,res),
 (n_557=0 & n=1 & -1+res=r_24' & R(n_557,r_24')) --> R(n,res),
 (1+n_557=n & -1+res=r_24' & 2<=n & R(n_557,r_24')) --> R(n,res)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure length$node SUCCESS

Termination checking result:

Stop Omega... 114 invocations 
9 false contexts at: ( (21,15)  (21,22)  (24,4)  (24,11)  (24,11)  (23,12)  (23,19)  (23,8)  (23,4) )

Total verification time: 0.28 second(s)
	Time spent in main process: 0.21 second(s)
	Time spent in child processes: 0.07 second(s)

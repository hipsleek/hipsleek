
Processing file "cll-insert.ss"
Parsing cll-insert.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure insert$node~int... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ n!=0]
!!! REL :  A(m,n)
!!! POST:  m>=2 & m=n+1
!!! PRE :  1<=n
!!! NEW RELS:[ (m=2 & n=1 | 1+n=m & 3<=m) --> A(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert$node~int SUCCESS

Termination checking result:

Stop Omega... 138 invocations 
0 false contexts at: ()

Total verification time: 0.42 second(s)
	Time spent in main process: 0.22 second(s)
	Time spent in child processes: 0.2 second(s)

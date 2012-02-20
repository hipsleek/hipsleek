
Processing file "dll-insert.ss"
Parsing dll-insert.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure insert$node2~int... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null, x!=null]
!!! REL :  A(m,n)
!!! POST:  n>=1 & n+1=m
!!! PRE :  1<=n
!!! NEW RELS:[ (n=1 & m=2) --> A(m,n),
 (1<=m_635 & 1+n_588=n & -1+m=m_635 & 1<=n & A(m_635,n_588)) --> A(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert$node2~int SUCCESS

Termination checking result:

Stop Omega... 137 invocations 
0 false contexts at: ()

Total verification time: 0.27 second(s)
	Time spent in main process: 0.21 second(s)
	Time spent in child processes: 0.06 second(s)

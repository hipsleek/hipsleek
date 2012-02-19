
Processing file "cll-insert.ss"
Parsing cll-insert.ss ...
Parsing /home2/loris/hg/sl_infer/prelude.ss ...
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

Stop Omega... 166 invocations 
0 false contexts at: ()

Total verification time: 0.34002 second(s)
	Time spent in main process: 0.056003 second(s)
	Time spent in child processes: 0.284017 second(s)

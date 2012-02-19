
Processing file "bug-3c.ss"
Parsing bug-3c.ss ...
Parsing /home2/loris/hg/sl_infer/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure append$node~node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ n!=0 | m!=0, n!=0 | m<=0, n!=0 | m!=0, n!=0 | m<=0]
!!! REL :  A(n,m,z)
!!! POST:  m>=0 & z>=(1+m) & z=n+m
!!! PRE :  0<=m & 1<=n
!!! NEW RELS:[ (1+m=z & 1<=z & n=1) --> A(n,m,z),
 (1<=z_580 & 1+n_557=n & m_558=m & -1+z=z_580 & 1<=n & 0<=m & 
  A(n_557,m_558,z_580)) --> A(n,m,z)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append$node~node SUCCESS

Termination checking result:

Stop Omega... 144 invocations 
0 false contexts at: ()

Total verification time: 0.156008 second(s)
	Time spent in main process: 0.056002 second(s)
	Time spent in child processes: 0.100006 second(s)

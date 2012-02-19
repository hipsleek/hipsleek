
Processing file "num-del.ss"
Parsing num-del.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure del$int~int... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ 2<=n, 1<=n]
!!! REL :  B(n,a,res)
!!! POST:  a>=1 & res>=a & res+1=n
!!! PRE :  1<=a & a<n
!!! NEW RELS:[ (a=1 & 1+res=n & 2<=n) --> B(n,a,res),
 ((1<=v_int_14_540 | v_int_14_540<=-1) & 
  B(v_int_14_539,v_int_14_540,v_int_14_544) & -1+res=v_int_14_544 & -1+
  a=v_int_14_540 & -1+n=v_int_14_539 & 0<=v_int_14_539) --> B(n,a,res)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del$int~int SUCCESS

Termination checking result:

Stop Omega... 114 invocations 
0 false contexts at: ()

Total verification time: 0.25 second(s)
	Time spent in main process: 0.18 second(s)
	Time spent in child processes: 0.07 second(s)


Processing file "bug-num-del.ss"
Parsing bug-num-del.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure del$int~int... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ 2<=n, 1<=n, 1<=n]
!!! REL :  B(n,a,res)
!!! POST:  a>=1 & res>=a & res+1=n
!!! PRE :  1<=a & a<n
!!! NEW RELS:[ (a=1 & 1+res=n & 2<=n) --> B(n,a,res),
 ((1<=v_int_27_543 | v_int_27_543<=-1) & 
  B(v_int_27_542,v_int_27_543,v_int_27_547) & -1+res=v_int_27_547 & -1+
  a=v_int_27_543 & -1+n=v_int_27_542 & 0<=v_int_27_542) --> B(n,a,res)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del$int~int SUCCESS

Termination checking result:

Stop Omega... 141 invocations 
0 false contexts at: ()

Total verification time: 0.23 second(s)
	Time spent in main process: 0.16 second(s)
	Time spent in child processes: 0.07 second(s)

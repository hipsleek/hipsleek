
Processing file "bug-del2.ss"
Parsing bug-del2.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure del$int... 
dprint: bug-del2.ss:9: ctx:  List of Failesc Context: [FEC(0, 0, 1  )]

Successful States:
[
 Label: 
 State:true&1<=n & n'+1=n&{FLOW,(20,21)=__norm}
       es_infer_vars/rel: [n]
       es_infer_pure: [1<=n]
       es_var_measures: MayLoop
 ]

!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ 2<=n, 1<=n]
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del$int SUCCESS

Termination checking result:

Stop Omega... 67 invocations 
0 false contexts at: ()

Total verification time: 0.17 second(s)
	Time spent in main process: 0.15 second(s)
	Time spent in child processes: 0.02 second(s)

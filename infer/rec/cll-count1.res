
Processing file "cll-count1.ss"
Parsing cll-count1.ss ...
Parsing /home2/loris/hg/sl_infer/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure count$node~node... 
dprint: cll-count1.ss:32: ctx:  List of Failesc Context: [FEC(0, 0, 1  [(61::,0 ); (61::,0 )])]

Successful States:
[
 Label: [(61::,0 ); (61::,0 )]
 State:x::cll<p,n>@M[Orig][LHSCase]&x'=x & h'=h & x'=h' & v_bool_31_539' & x'=h' & v_bool_31_539'&{FLOW,(20,21)=__norm}
       es_infer_vars/rel: [h; p]
       es_var_measures: MayLoop
 ]

dprint: cll-count1.ss:40: ctx:  List of Failesc Context: [FEC(0, 0, 1  [(61::,1 ); (61::,1 )])]

Successful States:
[
 Label: [(61::,1 ); (61::,1 )]
 State:false&false&{FLOW,(20,21)=__norm}
       es_infer_vars/rel: [h; p]
       es_var_measures: MayLoop
 ]

!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ p=h, p=h]
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure count$node~node SUCCESS

Termination checking result:

Stop Omega... 100 invocations 
8 false contexts at: ( (41,2)  (41,9)  (39,6)  (39,10)  (39,2)  (38,6)  (38,12)  (38,2) )

Total verification time: 0.104005 second(s)
	Time spent in main process: 0.044002 second(s)
	Time spent in child processes: 0.060003 second(s)

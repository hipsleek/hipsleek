
Processing file "bug-del2.ss"
Parsing bug-del2.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
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
!!! OLD SPECS: ((None,[]),EInfer [n]
              EBase true&true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::
                                true&true&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase true&2<=n & MayLoop&{FLOW,(1,23)=__flow}
                    EAssume 1::
                      true&2<=n&{FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del$int SUCCESS

Termination checking result:

Stop Omega... 66 invocations 
0 false contexts at: ()

Total verification time: 0.05 second(s)
	Time spent in main process: 0.03 second(s)
	Time spent in child processes: 0.02 second(s)

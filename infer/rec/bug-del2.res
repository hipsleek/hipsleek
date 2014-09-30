Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure del$int... 
dprint: bug-del2.ss:9: ctx:  List of Failesc Context: [FEC(0, 0, 1  )]

Successful States:
[
 Label: 
 State:emp&1<=n & n'+(1*1)=n&{FLOW,(22,23)=__norm}[]
       es_infer_vars/rel: [n]
       es_infer_pure: [1<=n]
       es_var_measures: MayLoop

 ]

!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ 2<=n, 1<=n]
!!! OLD SPECS: ((None,[]),EInfer [n]
              EBase emp&true&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 66::
                                emp&true&{FLOW,(22,23)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase emp&2<=n & MayLoop&{FLOW,(1,25)=__flow}[]
                    EAssume 66::
                      emp&2<=n&{FLOW,(22,23)=__norm}[])
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del$int SUCCESS

Termination checking result:

Stop Omega... 55 invocations 
0 false contexts at: ()

Total verification time: 0.19 second(s)
	Time spent in main process: 0.18 second(s)
	Time spent in child processes: 0.01 second(s)

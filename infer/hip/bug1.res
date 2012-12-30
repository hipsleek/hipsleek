Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure foo2$int... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ 2<=i]
!!! OLD SPECS: ((None,[]),EInfer [i]
              EBase emp&true&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 66::ref [i]
                                emp&true&{FLOW,(22,23)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase emp&2<=i & MayLoop&{FLOW,(1,25)=__flow}[]
                    EAssume 66::ref [i]
                      emp&(i-2)<=i' & i'<i & 2<=i&{FLOW,(22,23)=__norm}[])
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure foo2$int SUCCESS

Termination checking result:

Stop Omega... 46 invocations 
0 false contexts at: ()

Total verification time: 0.2 second(s)
	Time spent in main process: 0.18 second(s)
	Time spent in child processes: 0.02 second(s)

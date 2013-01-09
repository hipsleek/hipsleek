Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure del$int... 
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
Procedure del$int SUCCESS

Termination checking result:

Stop Omega... 58 invocations 
0 false contexts at: ()

Total verification time: 0.22 second(s)
	Time spent in main process: 0.2 second(s)
	Time spent in child processes: 0.02 second(s)


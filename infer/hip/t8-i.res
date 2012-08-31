Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure foo1$int... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ 1<=i]
!!! OLD SPECS: ((None,[]),EInfer [i]
              EBase true&true&{FLOW,(20,21)=__norm}[]
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                              EAssume 72::ref [i]
                                true&true&{FLOW,(20,21)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase true&1<=i & MayLoop&{FLOW,(1,23)=__flow}[]
                    EAssume 72::ref [i]
                      true&i'=i-1 & 1<=i&{FLOW,(20,21)=__norm}[])
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure foo1$int SUCCESS

Checking procedure foo1a$int... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ 1<=i]
!!! OLD SPECS: ((None,[]),EInfer [i]
              EBase true&true&{FLOW,(20,21)=__norm}[]
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                              EAssume 75::ref [i]
                                true&true&{FLOW,(20,21)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase true&1<=i & MayLoop&{FLOW,(1,23)=__flow}[]
                    EAssume 75::ref [i]
                      true&i'=i-1 & 1<=i&{FLOW,(20,21)=__norm}[])
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure foo1a$int SUCCESS

Checking procedure foo1b$int... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase true&0<i&{FLOW,(20,21)=__norm}[]
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                              EAssume 78::ref [i]
                                true&true&{FLOW,(20,21)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase true&1<=i&{FLOW,(20,21)=__norm}[]
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                            EAssume 78::ref [i]
                              true&i'=i-1 & 1<=i&{FLOW,(20,21)=__norm}[])
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure foo1b$int SUCCESS

Termination checking result:

Stop Omega... 68 invocations 
0 false contexts at: ()

Total verification time: 0.2 second(s)
	Time spent in main process: 0.18 second(s)
	Time spent in child processes: 0.02 second(s)

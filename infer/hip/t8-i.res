Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure foo1$int... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ 1<=i]
!!! OLD SPECS: ((None,[]),EInfer [i]
              EBase emp&true&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 72::ref [i]
                                emp&true&{FLOW,(22,23)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase emp&1<=i & MayLoop&{FLOW,(1,25)=__flow}[]
                    EAssume 72::ref [i]
                      emp&i'=i-1 & 1<=i&{FLOW,(22,23)=__norm}[])
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure foo1$int SUCCESS

Checking procedure foo1a$int... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ 1<=i]
!!! OLD SPECS: ((None,[]),EInfer [i]
              EBase emp&true&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 75::ref [i]
                                emp&true&{FLOW,(22,23)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase emp&1<=i & MayLoop&{FLOW,(1,25)=__flow}[]
                    EAssume 75::ref [i]
                      emp&i'=i-1 & 1<=i&{FLOW,(22,23)=__norm}[])
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure foo1a$int SUCCESS

Checking procedure foo1b$int... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase emp&0<i&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 78::ref [i]
                                emp&true&{FLOW,(22,23)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase emp&1<=i&{FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 78::ref [i]
                              emp&i'=i-1 & 1<=i&{FLOW,(22,23)=__norm}[])
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure foo1b$int SUCCESS

Termination checking result:

Stop Omega... 67 invocations 
0 false contexts at: ()

Total verification time: 0.21 second(s)
	Time spent in main process: 0.19 second(s)
	Time spent in child processes: 0.02 second(s)

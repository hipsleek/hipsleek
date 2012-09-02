Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure foo1$int... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ 1<=i]
!!! OLD SPECS: ((None,[]),EInfer [i]
              EBase emp&true&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 78::ref [i]
                                emp&true&{FLOW,(22,23)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase emp&1<=i & MayLoop&{FLOW,(1,25)=__flow}[]
                    EAssume 78::ref [i]
                      emp&i'=i-1 & 1<=i&{FLOW,(22,23)=__norm}[])
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure foo1$int SUCCESS

Checking procedure foo1a$int... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase emp&0<i&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 81::ref [i]
                                emp&true&{FLOW,(22,23)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase emp&1<=i&{FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 81::ref [i]
                              emp&i'=i-1 & 1<=i&{FLOW,(22,23)=__norm}[])
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure foo1a$int SUCCESS

Checking procedure foo1b$int... 
!!! OLD SPECS: ((None,[]),EInfer [i]
              EBase emp&0<i&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 84::ref [i]
                                emp&true&{FLOW,(22,23)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase emp&1<=i&{FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 84::ref [i]
                              emp&i'=i-1 & 1<=i&{FLOW,(22,23)=__norm}[])
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure foo1b$int SUCCESS

Checking procedure foo2$int... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ 2<=i]
!!! OLD SPECS: ((None,[]),EInfer [i]
              EBase emp&true&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 87::ref [i]
                                emp&true&{FLOW,(22,23)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase emp&2<=i & MayLoop&{FLOW,(1,25)=__flow}[]
                    EAssume 87::ref [i]
                      emp&(i-2)<=i' & i'<i & 2<=i&{FLOW,(22,23)=__norm}[])
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure foo2$int SUCCESS

Checking procedure foo2a$int... 
Proving precondition in method bnd$int Failed.
  (may) cause:  r_19'<=2 & 1<=r_19' |-  0<=i'. LOCS:[71;72;74] (may-bug)

Context of Verification Failure: File "t1-i.ss",Line:65,Col:10
Last Proving Location: File "t1-i.ss",Line:74,Col:2

Procedure foo2a$int FAIL-2

Exception Failure("Proving precond failed") Occurred!

Error(s) detected when checking procedure foo2a$int

Termination checking result:

Stop Omega... 86 invocations 
0 false contexts at: ()

Total verification time: 0.76 second(s)
	Time spent in main process: 0.74 second(s)
	Time spent in child processes: 0.02 second(s)

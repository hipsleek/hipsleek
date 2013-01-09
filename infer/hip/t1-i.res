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
                              emp&i=i'+1 & 0<=i'&{FLOW,(22,23)=__norm}[])
!!! NEW RELS:[]
!!! NEW ASSUME:[]
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
                              emp&i=i'+1 & 0<=i'&{FLOW,(22,23)=__norm}[])
!!! NEW RELS:[]
!!! NEW ASSUME:[]
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
Procedure foo2$int SUCCESS

Checking procedure foo2a$int... 
( ) :t1-i.ss:74: 2: Proving precondition in method failed


(Cause of PreCond Failure):t1-i.ss:74: 2:  List of Failesc Context: [FEC(1, 0, 0 )]
Failed States:
[
 Label: 
 State:
        fe_kind: MAY
        fe_name: logical bug
        fe_locs: {
                  fc_message: failed in entailing pure formula(s) in conseq
                  fc_current_lhs_flow: {FLOW,(22,23)=__norm}}
 ]

Context of Verification Failure: File "t1-i.ss",Line:65,Col:10
Last Proving Location: File "t1-i.ss",Line:74,Col:2

ERROR: at t1-i.ss_74_2 
Message: Proving precondition in method failed.
 
Procedure foo2a$int FAIL-2

Exception Failure("Proving precondition in method failed.") Occurred!

Error(s) detected when checking procedure foo2a$int

Termination checking result:

Stop Omega... 79 invocations 
0 false contexts at: ()

Total verification time: 0.83 second(s)
	Time spent in main process: 0.8 second(s)
	Time spent in child processes: 0.03 second(s)


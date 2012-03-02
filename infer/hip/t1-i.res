
Processing file "t1-i.ss"
Parsing t1-i.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure foo1$int... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ 1<=i]
!!! OLD SPECS: ((None,[]),EInfer [i]
              EBase true&true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::ref [i]
                                true&true&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase true&1<=i & MayLoop&{FLOW,(1,23)=__flow}
                    EAssume 1::ref [i]
                      true&i'=i-1 & 1<=i&{FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure foo1$int SUCCESS

Checking procedure foo1a$int... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase true&0<i&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 4::ref [i]
                                true&true&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase true&1<=i&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 4::ref [i]
                              true&i'=i-1 & 1<=i&{FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure foo1a$int SUCCESS

Checking procedure foo1b$int... 
!!! OLD SPECS: ((None,[]),EInfer [i]
              EBase true&0<i&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 7::ref [i]
                                true&true&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase true&1<=i&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 7::ref [i]
                              true&i'=i-1 & 1<=i&{FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure foo1b$int SUCCESS

Checking procedure foo2$int... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ 2<=i]
!!! OLD SPECS: ((None,[]),EInfer [i]
              EBase true&true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 10::ref [i]
                                true&true&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase true&2<=i & MayLoop&{FLOW,(1,23)=__flow}
                    EAssume 10::ref [i]
                      true&(i-2)<=i' & i'<i & 2<=i&{FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure foo2$int SUCCESS

Checking procedure foo2a$int... 
Procedure Call:t1-i.ss:74: 2: 
Verification Context:(Line:65,Col:10)
Proving precondition in method bnd$int for spec:
 ((None,[]),EBase true&0<=i'&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 16::
                              true&true&{FLOW,(20,21)=__norm})
Current States: [ true&1<=r_24' & r_24'<=2 & i'+r_24'=i&{FLOW,(20,21)=__norm}
 es_var_measures: MayLoop] has failed 


!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase true&true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 13::ref [i]
                                true&true&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase true&MayLoop&{FLOW,(1,23)=__flow}
                    EAssume 13::ref [i]
                      true&true&{FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure foo2a$int result FAIL-1

Termination checking result:

Stop Omega... 99 invocations 
0 false contexts at: ()

Total verification time: 0.06 second(s)
	Time spent in main process: 0.04 second(s)
	Time spent in child processes: 0.02 second(s)

Translating global variables to procedure parameters...

Checking procedure append$node~node... Starting Omega...oc

!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null, x!=null]
!!! REL :  A(S1,S2,S)
!!! POST:  union(S1,S2)=S
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [x,A]
              EBase exists (Expl)(Impl)[S1; 
                    S2](ex)x::ll<S1>@M[Orig][LHSCase]@ rem br[{191,190}] * 
                    y::ll<S2>@M[Orig][LHSCase]@ rem br[{191,190}]&(())&
                    {FLOW,(20,21)=__norm}[]
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                              EAssume 64::
                                EXISTS(S: x::ll<S>@M[Orig][LHSCase]@ rem br[{191,190}]&
                                (([A(S1,S2,S)]))&{FLOW,(20,21)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[S1; 
                  S2](ex)x::ll<S1>@M[Orig][LHSCase]@ rem br[{191,190}] * 
                  y::ll<S2>@M[Orig][LHSCase]@ rem br[{191,190}]&(())&
                  {FLOW,(20,21)=__norm}[]
                    EBase true&(([MayLoop][x!=null]))&{FLOW,(1,23)=__flow}[]
                            EAssume 64::
                              EXISTS(S: x::ll<S>@M[Orig][LHSCase]@ rem br[{191,190}]&
                              (([union(S1,S2)=S]))&{FLOW,(20,21)=__norm})[])
!!! NEW RELS:[ (exists(v_562:exists(S1_564:exists(v_585:exists(S1_587:S1_564= & 
  v_562=v_585 & S2=S1_587 & S=union(S1_587,{v_585}) & S1=union(S1_564,
  {v_562})))))) --> A(S1,S2,S),
 (exists(v_562:exists(S1_564:exists(v_592:exists(S1_594:S_591!=() & 
  S1_564!=() & S1_578=S1_564 & S1_594=S_591 & v_562=v_592 & 
  A(S1_578,S2_579,S_591) & S2=S2_579 & S=union(S1_594,{v_592}) & 
  S1=union(S1_564,{v_562})))))) --> A(S1,S2,S)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append$node~node SUCCESS

Termination checking result:


0 false contexts at: ()

Total verification time: 0.47 second(s)
	Time spent in main process: 0.25 second(s)
	Time spent in child processes: 0.22 second(s)

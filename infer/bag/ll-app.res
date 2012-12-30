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
                    S2](ex)x::ll<S1>@M[Orig][LHSCase]@ rem br[{199,198}] * 
                    y::ll<S2>@M[Orig][LHSCase]@ rem br[{199,198}]&(())&
                    {FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 64::
                                EXISTS(S: x::ll<S>@M[Orig][LHSCase]@ rem br[{199,198}]&
                                (([A(S1,S2,S)]))&{FLOW,(22,23)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[S1; 
                  S2](ex)x::ll<S1>@M[Orig][LHSCase]@ rem br[{199,198}] * 
                  y::ll<S2>@M[Orig][LHSCase]@ rem br[{199,198}]&(())&
                  {FLOW,(22,23)=__norm}[]
                    EBase emp&(([MayLoop][x!=null]))&{FLOW,(1,25)=__flow}[]
                            EAssume 64::
                              EXISTS(S: x::ll<S>@M[Orig][LHSCase]@ rem br[{199,198}]&
                              (([union(S1,S2)=S]))&{FLOW,(22,23)=__norm})[])
!!! NEW RELS:[ (exists(v_581:exists(S1_583:exists(v_604:exists(S1_606:S1_583= & 
  v_581=v_604 & S2=S1_606 & S=union(S1_606,{v_604}) & S1=union(S1_583,
  {v_581})))))) --> A(S1,S2,S),
 (exists(v_581:exists(S1_583:exists(v_611:exists(S1_613:S_610!=() & 
  S1_583!=() & S1_597=S1_583 & S1_613=S_610 & v_581=v_611 & 
  A(S1_597,S2_598,S_610) & S2=S2_598 & S=union(S1_613,{v_611}) & 
  S1=union(S1_583,{v_581})))))) --> A(S1,S2,S)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append$node~node SUCCESS

Termination checking result:


0 false contexts at: ()

Total verification time: 0.53 second(s)
	Time spent in main process: 0.3 second(s)
	Time spent in child processes: 0.23 second(s)

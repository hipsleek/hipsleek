/usr/local/bin/mona

Processing file "ll-app.ss"
Parsing ll-app.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
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
                    S2](ex)x::ll<S1>@M[Orig][LHSCase] * 
                    y::ll<S2>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::
                                EXISTS(S: x::ll<S>@M[Orig][LHSCase]&
                                A(S1,S2,S)&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[S1; 
                  S2](ex)x::ll<S1>@M[Orig][LHSCase] * 
                  y::ll<S2>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                    EBase true&x!=null & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 1::
                              EXISTS(S_640: x::ll<S_640>@M[Orig][LHSCase]&
                              union(S1,S2)=S_640&{FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_613:exists(v_612:exists(S1_595:exists(v_550:exists(v_593:exists(S1_552:(S2= | 
  S2=union(S1_613,{v_612})) & S=union(S1_595,{v_593}) & S1=union(S1_552,
  {v_550}) & S2=S1_595 & v_550=v_593 & S1_552=))))))) --> A(S1,S2,S),
 (exists(S1_633:exists(v_632:exists(S1_552:exists(v_550:exists(S1_620:exists(v_618:S_617=union(S1_633,
  {v_632}) & S_617=S1_620 & v_550=v_618 & S1_552=S1_566 & S2=S2_567 & 
  A(S1_566,S2_567,S_617) & S1=union(S1_552,{v_550}) & S=union(S1_620,
  {v_618})))))))) --> A(S1,S2,S)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append$node~node SUCCESS

Termination checking result:


0 false contexts at: ()

Total verification time: 0.29 second(s)
	Time spent in main process: 0.05 second(s)
	Time spent in child processes: 0.24 second(s)

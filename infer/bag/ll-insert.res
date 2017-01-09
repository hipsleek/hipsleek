Translating global variables to procedure parameters...

Checking procedure insert$node~int... Starting Omega...oc

Mona is running ... 

!!! REL :  A(S,S1,a)
!!! POST:  S1=union(S,{a})
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [A]
              EBase exists (Expl)(Impl)[S](ex)x::ll<S>@M[Orig][LHSCase]@ rem br[{198}]&
                    (([S!=()][null!=x]))&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 64::
                                EXISTS(S1: x::ll<S1>@M[Orig][LHSCase]@ rem br[{199,198}]&
                                (([A(S,S1,a)]))&{FLOW,(22,23)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[S](ex)x::ll<S>@M[Orig][LHSCase]@ rem br[{198}]&
                  (([S!=()][x!=null]))&{FLOW,(22,23)=__norm}[]
                    EBase emp&(([MayLoop]))&{FLOW,(1,25)=__flow}[]
                            EAssume 64::
                              EXISTS(S1: x::ll<S1>@M[Orig][LHSCase]@ rem br[{199,198}]&
                              (([S1=union(S,{a})]))&{FLOW,(22,23)=__norm})[])
!!! NEW RELS:[ (exists(v_582:exists(S1_584:exists(v_607:exists(S1_609:exists(v_612:exists(a':exists(S1_614:S1_614= & 
  S1_609=union(S1_614,{v_612}) & S1_584= & v_582=v_607 & a'=v_612 & 
  a=v_612 & S1=union(S1_609,{v_607}) & S=union(S1_584,{v_582}) & 
  S!=())))))))) --> A(S,S1,a),
 (exists(v_582:exists(S1_584:exists(v_621:exists(S1_623:S1_620!=() & 
  S1_584!=() & S1_584=S_599 & S1_623=S1_620 & v_582=v_621 & 
  A(S_599,S1_620,a) & S1=union(S1_623,{v_621}) & S=union(S1_584,{v_582}) & 
  S!=()))))) --> A(S,S1,a)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert$node~int SUCCESS

Termination checking result:


0 false contexts at: ()

Total verification time: 0.41 second(s)
	Time spent in main process: 0.28 second(s)
	Time spent in child processes: 0.13 second(s)

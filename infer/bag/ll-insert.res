Translating global variables to procedure parameters...

Checking procedure insert$node~int... Starting Omega...oc

Mona is running ... 

!!! REL :  A(S,S1,a)
!!! POST:  S1=union(S,{a})
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [A]
              EBase exists (Expl)(Impl)[S](ex)x::ll<S>@M[Orig][LHSCase]@ rem br[{190}]&
                    (([S!=()][null!=x]))&{FLOW,(20,21)=__norm}[]
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                              EAssume 64::
                                EXISTS(S1: x::ll<S1>@M[Orig][LHSCase]@ rem br[{191,190}]&
                                (([A(S,S1,a)]))&{FLOW,(20,21)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[S](ex)x::ll<S>@M[Orig][LHSCase]@ rem br[{190}]&
                  (([S!=()][x!=null]))&{FLOW,(20,21)=__norm}[]
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}[]
                            EAssume 64::
                              EXISTS(S1: x::ll<S1>@M[Orig][LHSCase]@ rem br[{191,190}]&
                              (([S1=union(S,{a})]))&{FLOW,(20,21)=__norm})[])
!!! NEW RELS:[ (exists(v_561:exists(S1_563:exists(v_586:exists(S1_588:exists(v_591:exists(a':exists(S1_593:S1_593= & 
  S1_588=union(S1_593,{v_591}) & S1_563= & v_561=v_586 & a'=v_591 & 
  a=v_591 & S1=union(S1_588,{v_586}) & S=union(S1_563,{v_561}) & 
  S!=())))))))) --> A(S,S1,a),
 (exists(v_561:exists(S1_563:exists(v_600:exists(S1_602:S1_599!=() & 
  S1_563!=() & S1_563=S_578 & S1_602=S1_599 & v_561=v_600 & 
  A(S_578,S1_599,a) & S1=union(S1_602,{v_600}) & S=union(S1_563,{v_561}) & 
  S!=()))))) --> A(S,S1,a)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert$node~int SUCCESS

Termination checking result:


0 false contexts at: ()

Total verification time: 0.39 second(s)
	Time spent in main process: 0.27 second(s)
	Time spent in child processes: 0.12 second(s)

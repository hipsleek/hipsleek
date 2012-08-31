Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure insert$node2~int... 
!!! REL :  A(mi,sm,a)
!!! POST:  sm>=mi & mi=a | a>=(1+mi) & mi=sm
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [A]
              EBase exists (Expl)(Impl)[sm; 
                    lg](ex)x::bst<sm,lg>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}[]
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                              EAssume 69::
                                EXISTS(mi,
                                ma: res::bst<mi,ma>@M[Orig][LHSCase]&
                                res!=null & A(mi,sm,a) & ma=max(lg,a)&
                                {FLOW,(20,21)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[sm; 
                  lg](ex)x::bst<sm,lg>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}[]
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                            EAssume 69::
                              EXISTS(mi,ma: res::bst<mi,ma>@M[Orig][LHSCase]&
                              res!=null & ma=max(lg,a) & (sm>=mi & mi=a | 
                              a>=(1+mi) & mi=sm)&{FLOW,(20,21)=__norm})[])
!!! NEW RELS:[ (a=mi & mi<=sm | mi=sm & sm<a) --> A(mi,sm,a),
 (mi_652=mi & a=a' & sm=sm_635 & A(mi_652,sm_635,a')) --> A(mi,sm,a),
 (sm=mi & a=a' & mi<=(a'-1) & mi<=sm_659 & 
  A(mi_676,sm_659,a')) --> A(mi,sm,a)]
!!! NEW ASSUME:[ RELASS [A]: ( A(mi_676,sm_659,a')) -->  a'<=(mi_676+1) | sm_659<=mi_676 & mi_676<=(a'-2)]
!!! NEW RANK:[]
Procedure insert$node2~int SUCCESS

Termination checking result:

Stop Omega... 148 invocations 
0 false contexts at: ()

Total verification time: 1.7 second(s)
	Time spent in main process: 0.43 second(s)
	Time spent in child processes: 1.27 second(s)

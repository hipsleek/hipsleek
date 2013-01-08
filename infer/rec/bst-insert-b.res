Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure insert$node2~int... 
!!! REL :  A(mi,sm,a)
!!! POST:  sm>=mi & mi=a | a>=(1+mi) & mi=sm
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [A]
              EBase exists (Expl)(Impl)[sm; 
                    lg](ex)x::bst<sm,lg>@M[Orig][LHSCase]&true&
                    {FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 69::
                                EXISTS(mi,
                                ma: res::bst<mi,ma>@M[Orig][LHSCase]&
                                res!=null & A(mi,sm,a) & ma=max(lg,a)&
                                {FLOW,(22,23)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[sm; 
                  lg](ex)x::bst<sm,lg>@M[Orig][LHSCase]&true&
                  {FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 69::
                              EXISTS(mi,ma: res::bst<mi,ma>@M[Orig][LHSCase]&
                              res!=null & ma=max(lg,a) & (sm>=mi & mi=a | 
                              a>=(1+mi) & mi=sm)&{FLOW,(22,23)=__norm})[])
!!! NEW RELS:[ (a=mi & mi<=sm | mi=sm & sm<a) --> A(mi,sm,a),
 (mi_669=mi & a=a' & sm=sm_652 & A(mi_669,sm_652,a')) --> A(mi,sm,a),
 (sm=mi & a=a' & mi<=(a'-1) & mi<=sm_676 & 
  A(mi_693,sm_676,a')) --> A(mi,sm,a)]
!!! NEW ASSUME:[ RELASS [A]: ( A(mi_693,sm_676,a')) -->  a'<=(mi_693+1) | sm_676<=mi_693 & mi_693<=(a'-2)]
!!! NEW RANK:[]
Procedure insert$node2~int SUCCESS

Termination checking result:

Stop Omega... 142 invocations 
0 false contexts at: ()

Total verification time: 1.76 second(s)
	Time spent in main process: 0.46 second(s)
	Time spent in child processes: 1.3 second(s)

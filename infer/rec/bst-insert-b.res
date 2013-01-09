Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure insert$node2~int... 
!!! REL :  A(mi,sm,a)
!!! POST:  (sm>=a & a=mi) | (a>=(1+mi) & mi=sm)
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
                              res!=null & ma=max(lg,a) & ((sm>=a & a=mi) | 
                              (a>=(1+mi) & mi=sm))&{FLOW,(22,23)=__norm})[])
!!! NEW RELS:[ ((mi=sm & mi<a) | (a=mi & a<=sm)) --> A(mi,sm,a),
 (mi=mi_663 & sm=sm_648 & A(mi_663,sm_648,a)) --> A(mi,sm,a),
 (mi=sm & mi<=(a-1) & mi<=sm_670 & A(mi_685,sm_670,a)) --> A(mi,sm,a)]
!!! NEW ASSUME:[ RELASS [A]: ( A(mi_685,sm_670,a)) -->  ((a-1)<=mi_685 & mi_685<sm_670) | sm_670<=mi_685]
Procedure insert$node2~int SUCCESS

Termination checking result:

Stop Omega... 141 invocations 
0 false contexts at: ()

Total verification time: 0.59 second(s)
	Time spent in main process: 0.36 second(s)
	Time spent in child processes: 0.23 second(s)



Processing file "bst-insert-b.ss"
Parsing bst-insert-b.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure insert$node2~int... 
!!! REL :  A(mi,sm,a)
!!! POST:  sm>=mi & mi=a | a>=(1+mi) & mi=sm
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [A]
              EBase exists (Expl)(Impl)[sm; 
                    lg](ex)x::bst<sm,lg>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::
                                EXISTS(mi,
                                ma: res::bst<mi,ma>@M[Orig][LHSCase]&
                                res!=null & A(mi,sm,a) & ma=max(lg,a)&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[sm; 
                  lg](ex)x::bst<sm,lg>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 1::
                              EXISTS(mi_802,
                              ma_803: res::bst<mi_802,ma_803>@M[Orig][LHSCase]&
                              res!=null & ma_803=max(lg,a) & (sm>=mi_802 & 
                              mi_802=a | a>=(1+mi_802) & mi_802=sm) & sm<=lg&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (a=mi & mi<=sm | mi=sm & sm<a) --> A(mi,sm,a),
 (mi_650=mi & sm=sm_622 & A(mi_650,sm_622,a)) --> A(mi,sm,a),
 (sm=mi & mi<=sm_657 & mi<=(a-1) & A(mi_685,sm_657,a)) --> A(mi,sm,a)]
!!! NEW ASSUME:[ RELASS [A]: ( A(mi_685,sm_657,a)) -->  a<=(mi_685+1) | sm_657<=mi_685 & mi_685<=(a-2)]
!!! NEW RANK:[]
Procedure insert$node2~int SUCCESS

Termination checking result:

Stop Omega... 184 invocations 
0 false contexts at: ()

Total verification time: 0.74 second(s)
	Time spent in main process: 0.08 second(s)
	Time spent in child processes: 0.66 second(s)

Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure delete$node2~int... 
!!! false ctx removed:[ hfalse&false&{FLOW,(22,23)=__norm}[]
 es_infer_vars/rel: [B]
 es_var_measures: MayLoop
]
!!! REL :  B(sm,s,l,lg)
!!! POST:  l>=s & l=lg & s=sm
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [B]
              EBase exists (Expl)(Impl)[sm; 
                    lg](ex)x::bst<sm,lg>@M[Orig][LHSCase]&true&
                    {FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 72::ref [x]
                                EXISTS(s,l: x'::bst<s,l>@M[Orig][LHSCase]&
                                B(sm,s,l,lg)&{FLOW,(22,23)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[sm; 
                  lg](ex)x::bst<sm,lg>@M[Orig][LHSCase]&true&
                  {FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 72::ref [x]
                              EXISTS(s,l: x'::bst<s,l>@M[Orig][LHSCase]&
                              l>=s & l=lg & s=sm&{FLOW,(22,23)=__norm})[])
!!! NEW RELS:[ (s=sm & l=lg & sm<=l) --> B(sm,s,l,lg),
 (s=sm & l=l_726 & lg=lg_642 & s<=sm_641 & sm_641<=s_725 & s_725<=l & 
  sm_641<=lg_642 & B(sm_641,s_725,l_726,lg_642)) --> B(sm,s,l,lg),
 (s=s_759 & l=lg & sm=sm_650 & l_760<=lg_651 & sm_650<=lg_651 & lg_651<=l & 
  s<=l_760 & B(sm_650,s_759,l_760,lg_651)) --> B(sm,s,l,lg),
 (s=sm & l=lg & s<=l) --> B(sm,s,l,lg)]
!!! NEW ASSUME:[ RELASS [B]: ( B(sm_641,s_725,l_726,lg_642)) -->  sm_641<=lg_642 & sm_641<=s_725,
 RELASS [B]: ( B(sm_650,s_759,l_760,lg_651)) -->  sm_650<=lg_651 & l_760<=lg_651]
Procedure delete$node2~int SUCCESS

Termination checking result:

Stop Omega... 168 invocations 
0 false contexts at: ()

Total verification time: 0.55 second(s)
	Time spent in main process: 0.41 second(s)
	Time spent in child processes: 0.14 second(s)


Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure delete$node2~int... 
!!! false ctx removed:[ hfalse&false&{FLOW,(22,23)=__norm}[]
 es_infer_vars/rel: [B]
 es_var_measures: MayLoop
]
!!! REL :  B(s,sm)
!!! POST:  s=sm
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [B]
              EBase exists (Expl)(Impl)[sm; 
                    lg](ex)x::bst<sm,lg>@M[Orig][LHSCase]&true&
                    {FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 72::ref [x]
                                EXISTS(l,s: x'::bst<s,l>@M[Orig][LHSCase]&
                                l<=lg & B(s,sm)&{FLOW,(22,23)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[sm; 
                  lg](ex)x::bst<sm,lg>@M[Orig][LHSCase]&true&
                  {FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 72::ref [x]
                              EXISTS(l,s: x'::bst<s,l>@M[Orig][LHSCase]&
                              l<=lg & s=sm&{FLOW,(22,23)=__norm})[])
!!! NEW RELS:[ (s=sm) --> B(s,sm),
 (s=sm & s<=sm_640 & sm_640<=s_725 & B(s_725,sm_640)) --> B(s,sm),
 (sm=sm_649 & s=s_759 & B(s_759,sm_649)) --> B(s,sm),
 (s=sm) --> B(s,sm)]
!!! NEW ASSUME:[ RELASS [B]: ( B(s_725,sm_640)) -->  sm_640<=s_725]
Procedure delete$node2~int SUCCESS

Termination checking result:

Stop Omega... 150 invocations 
0 false contexts at: ()

Total verification time: 0.5 second(s)
	Time spent in main process: 0.4 second(s)
	Time spent in child processes: 0.1 second(s)


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
                                sm<=s & l<=lg & B(sm,s,l,lg)&
                                {FLOW,(22,23)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[sm; 
                  lg](ex)x::bst<sm,lg>@M[Orig][LHSCase]&true&
                  {FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 72::ref [x]
                              EXISTS(s,l: x'::bst<s,l>@M[Orig][LHSCase]&
                              sm<=s & l<=lg & l>=s & l=lg & s=sm&
                              {FLOW,(22,23)=__norm})[])
!!! NEW RELS:[ (s=sm & l=lg & sm<=l) --> B(sm,s,l,lg),
 (s=sm & l=l_728 & lg=lg_644 & s<=sm_643 & sm_643<=s_727 & s_727<=l & 
  l<=lg_644 & B(sm_643,s_727,l_728,lg_644)) --> B(sm,s,l,lg),
 (sm=sm_652 & s=s_760 & l=lg & sm_652<=s & s<=l_761 & l_761<=lg_653 & 
  lg_653<=l & B(sm_652,s_760,l_761,lg_653)) --> B(sm,s,l,lg),
 (s=sm & l=lg & s<=l) --> B(sm,s,l,lg)]
!!! NEW ASSUME:[]
Procedure delete$node2~int SUCCESS

Termination checking result:

Stop Omega... 132 invocations 
0 false contexts at: ()

Total verification time: 0.47 second(s)
	Time spent in main process: 0.39 second(s)
	Time spent in child processes: 0.08 second(s)


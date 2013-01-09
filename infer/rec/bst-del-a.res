Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure delete$node2~int... 
!!! false ctx removed:[ hfalse&false&{FLOW,(22,23)=__norm}[]
 es_infer_vars/rel: [B]
 es_var_measures: MayLoop
]
!!! REL :  B(l,lg)
!!! POST:  l=lg
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [B]
              EBase exists (Expl)(Impl)[sm; 
                    lg](ex)x::bst<sm,lg>@M[Orig][LHSCase]&true&
                    {FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 72::ref [x]
                                EXISTS(s,l: x'::bst<s,l>@M[Orig][LHSCase]&
                                sm<=s & B(l,lg)&{FLOW,(22,23)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[sm; 
                  lg](ex)x::bst<sm,lg>@M[Orig][LHSCase]&true&
                  {FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 72::ref [x]
                              EXISTS(s,l: x'::bst<s,l>@M[Orig][LHSCase]&
                              sm<=s & l=lg&{FLOW,(22,23)=__norm})[])
!!! NEW RELS:[ (l=l_725 & lg=lg_641 & B(l_725,lg_641)) --> B(l,lg),
 (l=lg & l_758<=lg_650 & lg_650<=l & B(l_758,lg_650)) --> B(l,lg),
 (l=lg) --> B(l,lg)]
!!! NEW ASSUME:[ RELASS [B]: ( B(l_758,lg_650)) -->  l_758<=lg_650]
Procedure delete$node2~int SUCCESS

Termination checking result:

Stop Omega... 150 invocations 
0 false contexts at: ()

Total verification time: 0.5 second(s)
	Time spent in main process: 0.4 second(s)
	Time spent in child processes: 0.1 second(s)


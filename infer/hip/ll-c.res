Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure appif$node~node... 
!!! false ctx removed:[ hfalse&false&{FLOW,(22,23)=__norm}[]
 es_infer_vars/rel: [n1]
 es_var_measures: MayLoop
]
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ n1!=0, n1!=0]
!!! OLD SPECS: ((None,[]),EInfer [n1]
              EBase exists (Expl)(Impl)[n1](ex)x::ll<n1>@M[Orig][LHSCase]&
                    true&{FLOW,(22,23)=__norm}[]
                      ECase case {
                             n1=1 -> ((None,[]),EBase emp&MayLoop&
                                                      {FLOW,(1,25)=__flow}[]
                                                        EAssume 65::
                                                          emp&true&
                                                          {FLOW,(22,23)=__norm}[])
                             ;
                             n1!=1 -> ((None,[]),EBase emp&MayLoop&
                                                       {FLOW,(1,25)=__flow}[]
                                                         EAssume 66::
                                                           emp&true&
                                                           {FLOW,(22,23)=__norm}[])
                             
                             })
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n1](ex)x::ll<n1>@M[Orig][LHSCase]&true&
                  {FLOW,(22,23)=__norm}[]
                    ECase case {
                           n1=1 -> ((None,[]),EBase emp&MayLoop&
                                                    {FLOW,(1,25)=__flow}[]
                                                      EAssume 65::
                                                        EXISTS(Anon_562: 
                                                        x::node<Anon_562,y>@M[Orig]&
                                                        n1=1&
                                                        {FLOW,(22,23)=__norm})[])
                           ;
                           n1!=1 -> ((None,[]),EBase emp&(1<=n1 | n1<=(0-
                                                     1)) & MayLoop&
                                                     {FLOW,(1,25)=__flow}[]
                                                       EAssume 66::
                                                         EXISTS(Anon_586,
                                                         q_587,
                                                         flted_14_585: 
                                                         x::node<Anon_586,q_587>@M[Orig] * 
                                                         q_587::ll<flted_14_585>@M[Orig]&
                                                         (n1=flted_14_585+
                                                         1 & 
                                                         1<=flted_14_585 & 
                                                         q_587!=null) | 
                                                         (flted_14_585=0-1 & 
                                                         n1=0 & q_587!=null)&
                                                         {FLOW,(22,23)=__norm})[])
                           
                           })
!!! NEW RELS:[]
!!! NEW ASSUME:[]
Procedure appif$node~node SUCCESS

Termination checking result:

Stop Omega... 64 invocations 
3 false contexts at: ( (30,11)  (28,6)  (27,1) )

Total verification time: 0.27 second(s)
	Time spent in main process: 0.24 second(s)
	Time spent in child processes: 0.03 second(s)


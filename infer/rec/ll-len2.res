Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure length$node... 
!!! false ctx removed:[ hfalse&false&{FLOW,(16,17)=__Return}[]
 es_infer_vars/rel: [R]
 es_var_measures: MayLoop
]
!!! false ctx removed:[ hfalse&false&{FLOW,(16,17)=__Return}[]
 es_infer_vars/rel: [R]
 es_var_measures: MayLoop
]
!!! REL :  R(n,res)
!!! POST:  res>=0 & n=res
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [R]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@L[Orig][LHSCase]&true&
                    {FLOW,(22,23)=__norm}[]
                      ECase case {
                             n=0 -> ((None,[]),EBase emp&MayLoop&
                                                     {FLOW,(1,25)=__flow}[]
                                                       EAssume 65::
                                                         emp&R(n,res)&
                                                         {FLOW,(22,23)=__norm}[])
                             ;
                             n!=0 -> ((None,[]),EBase emp&MayLoop&
                                                      {FLOW,(1,25)=__flow}[]
                                                        EAssume 66::
                                                          emp&R(n,res)&
                                                          {FLOW,(22,23)=__norm}[])
                             
                             })
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@L[Orig][LHSCase]&true&
                  {FLOW,(22,23)=__norm}[]
                    ECase case {
                           n=0 -> ((None,[]),EBase emp&MayLoop&
                                                   {FLOW,(1,25)=__flow}[]
                                                     EAssume 65::
                                                       emp&res>=0 & n=res&
                                                       {FLOW,(22,23)=__norm}[])
                           ;
                           n!=0 -> ((None,[]),EBase emp&MayLoop&
                                                    {FLOW,(1,25)=__flow}[]
                                                      EAssume 66::
                                                        emp&res>=0 & n=res&
                                                        {FLOW,(22,23)=__norm}[])
                           
                           })
!!! NEW RELS:[ (n=0 & res=0) --> R(n,res),
 (n=1 & n_589=0 & r_604=res-1 & R(n_589,r_604)) --> R(n,res),
 (r_607=res-1 & n=n_589+1 & 1<=n_589 & R(n_589,r_607)) --> R(n,res)]
!!! NEW ASSUME:[]
Procedure length$node SUCCESS

Termination checking result:

Stop Omega... 65 invocations 
9 false contexts at: ( (21,15)  (21,22)  (24,4)  (24,11)  (24,11)  (23,12)  (23,19)  (23,8)  (22,7) )

Total verification time: 0.28 second(s)
	Time spent in main process: 0.23 second(s)
	Time spent in child processes: 0.05 second(s)


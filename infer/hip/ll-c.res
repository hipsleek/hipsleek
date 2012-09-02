Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure appif$node~node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ n1!=0]
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
                                                        EXISTS(x',Anon_563,
                                                        y': x'::node<Anon_563,y'>@M[Orig]&
                                                        x'=x & y'=y & n1=1&
                                                        {FLOW,(22,23)=__norm})[])
                           ;
                           n1!=1 -> ((None,[]),EBase emp&(1<=n1 | n1<=(0-
                                                     1)) & MayLoop&
                                                     {FLOW,(1,25)=__flow}[]
                                                       EAssume 66::
                                                         EXISTS(x',Anon_587,
                                                         q_588,
                                                         flted_14_586: 
                                                         x'::node<Anon_587,q_588>@M[Orig] * 
                                                         q_588::ll<flted_14_586>@M[Orig]&
                                                         x'=x & 
                                                         n1=flted_14_586+1 & 
                                                         1<=flted_14_586 & 
                                                         q_588!=null | 
                                                         x'=x & 
                                                         flted_14_586=0-1 & 
                                                         n1=0 & q_588!=null&
                                                         {FLOW,(22,23)=__norm})[])
                           
                           })
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure appif$node~node SUCCESS

Termination checking result:

Stop Omega... 65 invocations 
3 false contexts at: ( (30,11)  (28,6)  (27,1) )

Total verification time: 0.23 second(s)
	Time spent in main process: 0.2 second(s)
	Time spent in child processes: 0.03 second(s)

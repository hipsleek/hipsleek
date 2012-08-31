Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure appif$node~node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ n1!=0]
!!! OLD SPECS: ((None,[]),EInfer [n1]
              EBase exists (Expl)(Impl)[n1](ex)x::ll<n1>@M[Orig][LHSCase]&
                    true&{FLOW,(20,21)=__norm}[]
                      ECase case {
                             n1=1 -> ((None,[]),EBase true&MayLoop&
                                                      {FLOW,(1,23)=__flow}[]
                                                        EAssume 65::
                                                          true&true&
                                                          {FLOW,(20,21)=__norm}[])
                             ;
                             n1!=1 -> ((None,[]),EBase true&MayLoop&
                                                       {FLOW,(1,23)=__flow}[]
                                                         EAssume 66::
                                                           true&true&
                                                           {FLOW,(20,21)=__norm}[])
                             
                             })
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n1](ex)x::ll<n1>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}[]
                    ECase case {
                           n1=1 -> ((None,[]),EBase true&MayLoop&
                                                    {FLOW,(1,23)=__flow}[]
                                                      EAssume 65::
                                                        EXISTS(x',f_551,
                                                        Anon_543,
                                                        y': x'::node<Anon_543,y'>@M[Orig]&
                                                        x'=x & y'=y & n1=1&
                                                        {FLOW,(20,21)=__norm})[])
                           ;
                           n1!=1 -> ((None,[]),EBase true&(1<=n1 | n1<=(0-
                                                     1)) & MayLoop&
                                                     {FLOW,(1,23)=__flow}[]
                                                       EAssume 66::
                                                         EXISTS(x',Anon_567,
                                                         q_568,
                                                         flted_14_566: 
                                                         x'::node<Anon_567,q_568>@M[Orig] * 
                                                         q_568::ll<flted_14_566>@M[Orig]&
                                                         x'=x & 
                                                         n1=flted_14_566+1 & 
                                                         1<=flted_14_566 & 
                                                         q_568!=null | 
                                                         x'=x & 
                                                         flted_14_566=0-1 & 
                                                         n1=0 & q_568!=null&
                                                         {FLOW,(20,21)=__norm})[])
                           
                           })
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure appif$node~node SUCCESS

Termination checking result:

Stop Omega... 68 invocations 
2 false contexts at: ( (30,11)  (27,1) )

Total verification time: 0.21 second(s)
	Time spent in main process: 0.19 second(s)
	Time spent in child processes: 0.02 second(s)

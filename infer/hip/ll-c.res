
Processing file "ll-c.ss"
Parsing ll-c.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure appif$node~node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ n1!=0]
!!! OLD SPECS: ((None,[]),EInfer [n1]
              EBase exists (Expl)(Impl)[n1](ex)x::ll<n1>@M[Orig][LHSCase]&
                    true&{FLOW,(20,21)=__norm}
                      ECase case {
                             n1=1 -> ((None,[]),EBase true&MayLoop&
                                                      {FLOW,(1,23)=__flow}
                                                        EAssume 1::
                                                          true&true&
                                                          {FLOW,(20,21)=__norm})
                             ;
                             n1!=1 -> ((None,[]),EBase true&MayLoop&
                                                       {FLOW,(1,23)=__flow}
                                                         EAssume 2::
                                                           true&true&
                                                           {FLOW,(20,21)=__norm})
                             
                             })
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n1](ex)x::ll<n1>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    ECase case {
                           n1=1 -> ((None,[]),EBase true&MayLoop&
                                                    {FLOW,(1,23)=__flow}
                                                      EAssume 1::
                                                        EXISTS(f_563,
                                                        Anon_564: x::node<Anon_564,y>@M[Orig]&
                                                        n1=1 & n1=1 & 0<=n1&
                                                        {FLOW,(20,21)=__norm}))
                           ;
                           n1!=1 -> ((None,[]),EBase true&(1<=n1 | n1<=(0-
                                                     1)) & MayLoop&
                                                     {FLOW,(1,23)=__flow}
                                                       EAssume 2::
                                                         EXISTS(Anon_565,
                                                         q_566,
                                                         flted_14_567: 
                                                         x::node<Anon_565,q_566>@M[Orig] * 
                                                         q_566::ll<flted_14_567>@M[Orig]&
                                                         (flted_14_567=n1-
                                                         1 & q_566!=null & 
                                                         2<=n1 | 
                                                         flted_14_567=n1-1 & 
                                                         n1<=0 & 
                                                         q_566!=null) & 
                                                         n1!=1 & 0<=n1&
                                                         {FLOW,(20,21)=__norm}))
                           
                           })
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure appif$node~node SUCCESS

Termination checking result:

Stop Omega... 70 invocations 
2 false contexts at: ( (30,11)  (27,1) )

Total verification time: 0.06 second(s)
	Time spent in main process: 0.04 second(s)
	Time spent in child processes: 0.02 second(s)

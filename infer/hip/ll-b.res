Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure appif$node~node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ n1!=0, n1!=0]
!!! OLD SPECS: ((None,[]),EInfer [n1]
              EBase exists (Expl)(Impl)[n1](ex)x::ll<n1>@M[Orig][LHSCase]&
                    true&{FLOW,(20,21)=__norm}[]
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                              EAssume 64::
                                true&true&{FLOW,(20,21)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n1](ex)x::ll<n1>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}[]
                    EBase true&(1<=n1 | n1<=(0-1)) & MayLoop&
                          {FLOW,(1,23)=__flow}[]
                            EAssume 64::
                              
                              EXISTS(x',f_550,Anon_541,
                              y': x'::node<Anon_541,y'>@M[Orig]&x'=x & 
                              y'=y & 0<=n1&{FLOW,(20,21)=__norm})[]
                              or EXISTS(x',Anon_541,q_542,
                                 flted_14_540: x'::node<Anon_541,q_542>@M[Orig] * 
                                 q_542::ll<flted_14_540>@M[Orig]&x'=x & 
                                 n1=flted_14_540+1 & q_542!=null & 0<=(1+
                                 flted_14_540)&{FLOW,(20,21)=__norm})[]
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure appif$node~node SUCCESS

Termination checking result:

Stop Omega... 64 invocations 
0 false contexts at: ()

Total verification time: 0.21 second(s)
	Time spent in main process: 0.19 second(s)
	Time spent in child processes: 0.02 second(s)

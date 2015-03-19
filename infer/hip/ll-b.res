Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure appif$node~node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ n1!=0, n1!=0]
!!! OLD SPECS: ((None,[]),EInfer [n1]
              EBase exists (Expl)(Impl)[n1](ex)x::ll<n1>@M[Orig][LHSCase]&
                    true&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 64::
                                emp&true&{FLOW,(22,23)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n1](ex)x::ll<n1>@M[Orig][LHSCase]&true&
                  {FLOW,(22,23)=__norm}[]
                    EBase emp&(1<=n1 | n1<=(0-1)) & MayLoop&
                          {FLOW,(1,25)=__flow}[]
                            EAssume 64::
                              
                              EXISTS(x',Anon_561,
                              y': x'::node<Anon_561,y'>@M[Orig]&x'=x & 
                              y'=y & 0<=n1&{FLOW,(22,23)=__norm})[]
                              or EXISTS(x',Anon_561,q_562,
                                 flted_14_560: x'::node<Anon_561,q_562>@M[Orig] * 
                                 q_562::ll<flted_14_560>@M[Orig]&x'=x & 
                                 n1=flted_14_560+1 & q_562!=null & 0<=(1+
                                 flted_14_560)&{FLOW,(22,23)=__norm})[]
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure appif$node~node SUCCESS

Termination checking result:

Stop Omega... 60 invocations 
0 false contexts at: ()

Total verification time: 0.22 second(s)
	Time spent in main process: 0.2 second(s)
	Time spent in child processes: 0.02 second(s)

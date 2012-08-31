Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure hd$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ n!=0]
!!! OLD SPECS: ((None,[]),EInfer [n]
              EBase exists (Expl)(Impl)[v; 
                    n](ex)x::llf<v,n>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}[]
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                              EAssume 62::
                                true&true&{FLOW,(20,21)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[v; n](ex)x::llf<v,n>@M[Orig][LHSCase]&
                  true&{FLOW,(20,21)=__norm}[]
                    EBase true&(1<=n | n<=(0-1)) & MayLoop&
                          {FLOW,(1,23)=__flow}[]
                            EAssume 62::
                              EXISTS(x',v_544,q_546,Anon_547,
                              flted_8_545: x'::node<v_544,q_546>@M[Orig] * 
                              q_546::llf<Anon_547,flted_8_545>@M[Orig]&
                              x'=x & res=v_544 & v=v_544 & n=flted_8_545+1 & 
                              0<=(1+flted_8_545)&{FLOW,(20,21)=__norm})[])
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure hd$node SUCCESS

Termination checking result:

Stop Omega... 47 invocations 
0 false contexts at: ()

Total verification time: 0.19 second(s)
	Time spent in main process: 0.17 second(s)
	Time spent in child processes: 0.02 second(s)

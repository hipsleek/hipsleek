Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure hd$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ n!=0]
!!! OLD SPECS: ((None,[]),EInfer [n]
              EBase exists (Expl)(Impl)[v; 
                    n](ex)x::llf<v,n>@M[Orig][LHSCase]&true&
                    {FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 62::
                                emp&true&{FLOW,(22,23)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[v; n](ex)x::llf<v,n>@M[Orig][LHSCase]&
                  true&{FLOW,(22,23)=__norm}[]
                    EBase emp&(1<=n | n<=(0-1)) & MayLoop&
                          {FLOW,(1,25)=__flow}[]
                            EAssume 62::
                              EXISTS(v_564,q_566,Anon_567,
                              flted_8_565: x::node<v_564,q_566>@M[Orig] * 
                              q_566::llf<Anon_567,flted_8_565>@M[Orig]&
                              res=v_564 & v=v_564 & n=flted_8_565+1 & 0<=(1+
                              flted_8_565)&{FLOW,(22,23)=__norm})[])
!!! NEW RELS:[]
!!! NEW ASSUME:[]
Procedure hd$node SUCCESS

Termination checking result:

Stop Omega... 48 invocations 
0 false contexts at: ()

Total verification time: 0.24 second(s)
	Time spent in main process: 0.22 second(s)
	Time spent in child processes: 0.02 second(s)


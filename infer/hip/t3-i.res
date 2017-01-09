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
                              EXISTS(x',v_565,q_567,Anon_568,
                              flted_8_566: x'::node<v_565,q_567>@M[Orig] * 
                              q_567::llf<Anon_568,flted_8_566>@M[Orig]&
                              x'=x & res=v_565 & v=v_565 & n=flted_8_566+1 & 
                              0<=(1+flted_8_566)&{FLOW,(22,23)=__norm})[])
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure hd$node SUCCESS

Termination checking result:

Stop Omega... 45 invocations 
0 false contexts at: ()

Total verification time: 0.2 second(s)
	Time spent in main process: 0.18 second(s)
	Time spent in child processes: 0.02 second(s)

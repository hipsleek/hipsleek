
Processing file "t3-i.ss"
Parsing t3-i.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure hd$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ n!=0]
!!! OLD SPECS: ((None,[]),EInfer [n]
              EBase exists (Expl)(Impl)[v; 
                    n](ex)x::llf<v,n>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::
                                true&true&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[v; n](ex)x::llf<v,n>@M[Orig][LHSCase]&
                  true&{FLOW,(20,21)=__norm}
                    EBase true&(1<=n | n<=(0-1)) & MayLoop&
                          {FLOW,(1,23)=__flow}
                            EAssume 1::
                              EXISTS(v_536,q_537,Anon_538,
                              flted_8_539: x::node<v_536,q_537>@M[Orig] * 
                              q_537::llf<Anon_538,flted_8_539>@M[Orig]&
                              flted_8_539=n-1 & res=v_536 & v=v_536 & 0<=n&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure hd$node SUCCESS

Termination checking result:

Stop Omega... 51 invocations 
0 false contexts at: ()

Total verification time: 0.06 second(s)
	Time spent in main process: 0.04 second(s)
	Time spent in child processes: 0.02 second(s)

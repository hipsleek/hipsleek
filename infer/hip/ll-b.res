
Processing file "ll-b.ss"
Parsing ll-b.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure appif$node~node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ n1!=0, n1!=0]
!!! OLD SPECS: ((None,[]),EInfer [n1]
              EBase exists (Expl)(Impl)[n1](ex)x::ll<n1>@M[Orig][LHSCase]&
                    true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::
                                true&true&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n1](ex)x::ll<n1>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&(1<=n1 | n1<=(0-1)) & MayLoop&
                          {FLOW,(1,23)=__flow}
                            EAssume 1::
                              
                              EXISTS(f_538,
                              Anon_539: x::node<Anon_539,y>@M[Orig]&0<=n1&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(Anon_540,q_541,
                                 flted_14_542: x::node<Anon_540,q_541>@M[Orig] * 
                                 q_541::ll<flted_14_542>@M[Orig]&
                                 flted_14_542=n1-1 & q_541!=null & 0<=n1&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure appif$node~node SUCCESS

Termination checking result:

Stop Omega... 65 invocations 
0 false contexts at: ()

Total verification time: 0.06 second(s)
	Time spent in main process: 0.04 second(s)
	Time spent in child processes: 0.02 second(s)

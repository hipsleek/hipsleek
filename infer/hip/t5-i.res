
Processing file "t5-i.ss"
Parsing t5-i.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure hd$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::
                                true&true&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&x!=null & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 1::
                              EXISTS(Anon_539,q_540,
                              flted_7_541: x::node<Anon_539,q_540>@M[Orig] * 
                              q_540::ll<flted_7_541>@M[Orig]&flted_7_541=n-
                              1 & Anon_539=res & 0<=n&{FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure hd$node SUCCESS

Checking procedure tl$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[ x::node<inf_val_38_545,inf_next_38_546>@inf_ann_544[Orig]]
!!! Inferred Pure :[]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase true&true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 4::
                                true&true&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase x::node<inf_val_38_545,inf_next_38_546>@L[Orig]&MayLoop&
                  {FLOW,(1,23)=__flow}
                    EAssume 4::
                      true&inf_next_38_546=res&{FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure tl$node SUCCESS

Checking procedure hdtl$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[ inf_inf_next_38_556::ll<inf_n_562>@inf_ann_561[Orig][LHSCase], x::node<inf_inf_val_38_555,inf_inf_next_38_556>@inf_ann_554[Orig]]
!!! Inferred Pure :[ inf_inf_next_38_556!=null, inf_ann_561<=0]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase true&true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 2::ref [x]
                                true&true&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase inf_inf_next_38_556::ll<inf_n_562>@M[Orig][LHSCase] * 
                  x::node<inf_inf_val_38_555,inf_inf_next_38_556>@L[Orig]&
                  inf_inf_next_38_556!=null & MayLoop&{FLOW,(1,23)=__flow}
                    EAssume 2::ref [x]
                      EXISTS(v_int_30_573,q_574,
                      flted_7_575: x'::node<v_int_30_573,q_574>@M[Orig] * 
                      q_574::ll<flted_7_575>@M[Orig]&res=v_int_30_573 & 
                      x'=inf_inf_next_38_556 & inf_n_562=flted_7_575+1 & 
                      0<=(1+flted_7_575) & inf_inf_next_38_556!=null & 
                      0<=inf_n_562&{FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure hdtl$node SUCCESS

Termination checking result:

Stop Omega... 100 invocations 
0 false contexts at: ()

Total verification time: 0.07 second(s)
	Time spent in main process: 0.05 second(s)
	Time spent in child processes: 0.02 second(s)

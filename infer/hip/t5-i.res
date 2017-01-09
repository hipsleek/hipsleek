Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure hd$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]&true&
                    {FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 65::
                                emp&true&{FLOW,(22,23)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]&true&
                  {FLOW,(22,23)=__norm}[]
                    EBase emp&x!=null & MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 65::
                              EXISTS(x',Anon_568,q_569,
                              flted_7_567: x'::node<Anon_568,q_569>@M[Orig] * 
                              q_569::ll<flted_7_567>@M[Orig]&x'=x & 
                              Anon_568=res & n=flted_7_567+1 & 0<=(1+
                              flted_7_567)&{FLOW,(22,23)=__norm})[])
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure hd$node SUCCESS

Checking procedure tl$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[ x::node<inf_val_38_575,inf_next_38_576>@inf_ann_574[Orig]]
!!! Inferred Pure :[]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase emp&true&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 68::
                                emp&true&{FLOW,(22,23)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase x::node<inf_val_38_575,inf_next_38_576>@L[Orig]&MayLoop&
                  {FLOW,(1,25)=__flow}[]
                    EAssume 68::
                      emp&inf_next_38_576=res&{FLOW,(22,23)=__norm}[])
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure tl$node SUCCESS

Checking procedure hdtl$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[ inf_inf_next_38_585::ll<inf_n_592>@inf_ann_591[Orig][LHSCase], x::node<inf_inf_val_38_584,inf_inf_next_38_585>@inf_ann_583[Orig]]
!!! Inferred Pure :[ inf_inf_next_38_585!=null, inf_ann_591<=0]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase emp&true&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 66::ref [x]
                                emp&true&{FLOW,(22,23)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase inf_inf_next_38_585::ll<inf_n_592>@M[Orig][LHSCase] * 
                  x::node<inf_inf_val_38_584,inf_inf_next_38_585>@L[Orig]&
                  inf_inf_next_38_585!=null & MayLoop&{FLOW,(1,25)=__flow}[]
                    EAssume 66::ref [x]
                      EXISTS(v_int_30_538',q_602,
                      flted_7_603: x'::node<v_int_30_538',q_602>@M[Orig] * 
                      q_602::ll<flted_7_603>@M[Orig]&res=v_int_30_538' & 
                      x'=inf_inf_next_38_585 & inf_n_592=flted_7_603+1 & 
                      0<=(1+flted_7_603) & inf_inf_next_38_585!=null&
                      {FLOW,(22,23)=__norm})[])
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure hdtl$node SUCCESS

Termination checking result:

Stop Omega... 90 invocations 
0 false contexts at: ()

Total verification time: 0.24 second(s)
	Time spent in main process: 0.21 second(s)
	Time spent in child processes: 0.03 second(s)

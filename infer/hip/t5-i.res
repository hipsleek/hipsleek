Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure hd$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}[]
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                              EAssume 65::
                                true&true&{FLOW,(20,21)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}[]
                    EBase true&x!=null & MayLoop&{FLOW,(1,23)=__flow}[]
                            EAssume 65::
                              EXISTS(x',Anon_549,q_550,
                              flted_7_548: x'::node<Anon_549,q_550>@M[Orig] * 
                              q_550::ll<flted_7_548>@M[Orig]&x'=x & 
                              Anon_549=res & n=flted_7_548+1 & 0<=(1+
                              flted_7_548)&{FLOW,(20,21)=__norm})[])
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure hd$node SUCCESS

Checking procedure tl$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[ x::node<inf_val_38_556,inf_next_38_557>@inf_ann_555[Orig]]
!!! Inferred Pure :[]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase true&true&{FLOW,(20,21)=__norm}[]
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                              EAssume 68::
                                true&true&{FLOW,(20,21)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase x::node<inf_val_38_556,inf_next_38_557>@L[Orig]&MayLoop&
                  {FLOW,(1,23)=__flow}[]
                    EAssume 68::
                      true&inf_next_38_557=res&{FLOW,(20,21)=__norm}[])
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure tl$node SUCCESS

Checking procedure hdtl$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[ inf_inf_next_38_567::ll<inf_n_574>@inf_ann_573[Orig][LHSCase], x::node<inf_inf_val_38_566,inf_inf_next_38_567>@inf_ann_565[Orig]]
!!! Inferred Pure :[ inf_inf_next_38_567!=null, inf_ann_573<=0]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase true&true&{FLOW,(20,21)=__norm}[]
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                              EAssume 66::ref [x]
                                true&true&{FLOW,(20,21)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase inf_inf_next_38_567::ll<inf_n_574>@M[Orig][LHSCase] * 
                  x::node<inf_inf_val_38_566,inf_inf_next_38_567>@L[Orig]&
                  inf_inf_next_38_567!=null & MayLoop&{FLOW,(1,23)=__flow}[]
                    EAssume 66::ref [x]
                      EXISTS(v_int_30_519',q_584,
                      flted_7_585: x'::node<v_int_30_519',q_584>@M[Orig] * 
                      q_584::ll<flted_7_585>@M[Orig]&res=v_int_30_519' & 
                      x'=inf_inf_next_38_567 & inf_n_574=flted_7_585+1 & 
                      0<=(1+flted_7_585) & inf_inf_next_38_567!=null&
                      {FLOW,(20,21)=__norm})[])
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure hdtl$node SUCCESS

Termination checking result:

Stop Omega... 93 invocations 
0 false contexts at: ()

Total verification time: 0.22 second(s)
	Time spent in main process: 0.2 second(s)
	Time spent in child processes: 0.02 second(s)

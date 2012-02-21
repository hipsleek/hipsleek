
Processing file "t5-i.ss"
Parsing t5-i.ss ...
Parsing ../../prelude.ss ...
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
                              x::node<Anon_535,q_536>@M[Orig] * 
                              q_536::ll<flted_7_534>@M[Orig]&n=flted_7_534+
                              1 & res=Anon_535 & 0<=n&{FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure hd$node SUCCESS

Checking procedure tl$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[ x::node<inf_val_38_542,inf_next_38_543>@inf_ann_541[Orig]]
!!! Inferred Pure :[]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase true&true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 4::
                                true&true&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase x::node<inf_val_38_542,inf_next_38_543>@L[Orig]&MayLoop&
                  {FLOW,(1,23)=__flow}
                    EAssume 4::
                      true&res=inf_next_38_543&{FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure tl$node SUCCESS

Checking procedure hdtl$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[ inf_inf_next_38_553::ll<inf_n_559>@inf_ann_558[Orig][LHSCase], x::node<inf_inf_val_38_552,inf_inf_next_38_553>@inf_ann_551[Orig]]
!!! Inferred Pure :[ inf_inf_next_38_553!=null, inf_ann_558<=0]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase true&true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 2::ref [x]
                                true&true&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase inf_inf_next_38_553::ll<inf_n_559>@M[Orig][LHSCase] * 
                  x::node<inf_inf_val_38_552,inf_inf_next_38_553>@L[Orig]&
                  inf_inf_next_38_553!=null & MayLoop&{FLOW,(1,23)=__flow}
                    EAssume 2::ref [x]
                      x'::node<Anon_535,q_536>@M[Orig] * 
                      q_536::ll<flted_7_534>@M[Orig]&inf_ann_558<=0 & 
                      inf_inf_next_38_553=x' & flted_7_534=inf_n_559-1 & 
                      res=Anon_535 & x'!=null & 0<=inf_n_559 & 0<=inf_n_559&
                      {FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure hdtl$node SUCCESS

Termination checking result:

Stop Omega... 108 invocations 
0 false contexts at: ()

Total verification time: 0.21 second(s)
	Time spent in main process: 0.18 second(s)
	Time spent in child processes: 0.03 second(s)

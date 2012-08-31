Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure hd$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[ x::node<inf_val_17_524,inf_next_17_525>@inf_ann_523[Orig]]
!!! Inferred Pure :[]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase true&true&{FLOW,(20,21)=__norm}[]
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                              EAssume 65::
                                true&true&{FLOW,(20,21)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase x::node<inf_val_17_524,inf_next_17_525>@L[Orig]&MayLoop&
                  {FLOW,(1,23)=__flow}[]
                    EAssume 65::
                      true&inf_val_17_524=res&{FLOW,(20,21)=__norm}[])
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure hd$node SUCCESS

Checking procedure tl$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[ x::node<inf_val_25_531,inf_next_25_532>@inf_ann_530[Orig]]
!!! Inferred Pure :[]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase true&true&{FLOW,(20,21)=__norm}[]
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                              EAssume 66::
                                true&true&{FLOW,(20,21)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase x::node<inf_val_25_531,inf_next_25_532>@L[Orig]&MayLoop&
                  {FLOW,(1,23)=__flow}[]
                    EAssume 66::
                      true&inf_next_25_532=res&{FLOW,(20,21)=__norm}[])
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure tl$node SUCCESS

Checking procedure hdtl$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[ inf_inf_next_25_542::node<inf_inf_val_17_550,inf_inf_next_17_551>@inf_ann_549[Orig], x::node<inf_inf_val_25_541,inf_inf_next_25_542>@inf_ann_540[Orig]]
!!! Inferred Pure :[]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase true&true&{FLOW,(20,21)=__norm}[]
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                              EAssume 67::ref [x]
                                true&true&{FLOW,(20,21)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase inf_inf_next_25_542::node<inf_inf_val_17_550,inf_inf_next_17_551>@L[Orig] * 
                  x::node<inf_inf_val_25_541,inf_inf_next_25_542>@L[Orig]&
                  MayLoop&{FLOW,(1,23)=__flow}[]
                    EAssume 67::ref [x]
                      true&inf_inf_next_25_542=x' & inf_inf_val_17_550=res&
                      {FLOW,(20,21)=__norm}[])
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure hdtl$node SUCCESS

Termination checking result:

Stop Omega... 46 invocations 
0 false contexts at: ()

Total verification time: 0.19 second(s)
	Time spent in main process: 0.18 second(s)
	Time spent in child processes: 0.01 second(s)

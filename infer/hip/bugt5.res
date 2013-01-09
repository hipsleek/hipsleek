Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure hd$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[ x::node<inf_val_17_541,inf_next_17_542>@inf_ann_540[Orig]]
!!! Inferred Pure :[]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase emp&true&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 65::
                                emp&true&{FLOW,(22,23)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase x::node<inf_val_17_541,inf_next_17_542>@L[Orig]&MayLoop&
                  {FLOW,(1,25)=__flow}[]
                    EAssume 65::
                      emp&inf_val_17_541=res&{FLOW,(22,23)=__norm}[])
!!! NEW RELS:[]
!!! NEW ASSUME:[]
Procedure hd$node SUCCESS

Checking procedure tl$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[ x::node<inf_val_25_548,inf_next_25_549>@inf_ann_547[Orig]]
!!! Inferred Pure :[]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase emp&true&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 66::
                                emp&true&{FLOW,(22,23)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase x::node<inf_val_25_548,inf_next_25_549>@L[Orig]&MayLoop&
                  {FLOW,(1,25)=__flow}[]
                    EAssume 66::
                      emp&inf_next_25_549=res&{FLOW,(22,23)=__norm}[])
!!! NEW RELS:[]
!!! NEW ASSUME:[]
Procedure tl$node SUCCESS

Checking procedure hdtl$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[ inf_inf_next_25_557::node<inf_inf_val_17_564,inf_inf_next_17_565>@inf_ann_563[Orig], x::node<inf_inf_val_25_556,inf_inf_next_25_557>@inf_ann_555[Orig]]
!!! Inferred Pure :[]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase emp&true&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 67::ref [x]
                                emp&true&{FLOW,(22,23)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase inf_inf_next_25_557::node<inf_inf_val_17_564,inf_inf_next_17_565>@L[Orig] * 
                  x::node<inf_inf_val_25_556,inf_inf_next_25_557>@L[Orig]&
                  MayLoop&{FLOW,(1,25)=__flow}[]
                    EAssume 67::ref [x]
                      emp&inf_inf_next_25_557=x' & inf_inf_val_17_564=res&
                      {FLOW,(22,23)=__norm}[])
!!! NEW RELS:[]
!!! NEW ASSUME:[]
Procedure hdtl$node SUCCESS

Termination checking result:

Stop Omega... 50 invocations 
0 false contexts at: ()

Total verification time: 0.25 second(s)
	Time spent in main process: 0.23 second(s)
	Time spent in child processes: 0.02 second(s)


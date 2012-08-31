Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure hd$node... 
Procedure hd$node SUCCESS

Checking procedure tl$node... 
Procedure tl$node SUCCESS

Checking procedure hdtl$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[ inf_b_544::node<inf_a_550,inf_Anon_551>@inf_ann_549[Orig], x::node<inf_Anon_543,inf_b_544>@inf_ann_542[Orig]]
!!! Inferred Pure :[]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase true&true&{FLOW,(20,21)=__norm}[]
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                              EAssume 67::ref [x]
                                true&true&{FLOW,(20,21)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase inf_b_544::node<inf_a_550,inf_Anon_551>@L[Orig] * 
                  x::node<inf_Anon_543,inf_b_544>@L[Orig]&MayLoop&
                  {FLOW,(1,23)=__flow}[]
                    EAssume 67::ref [x]
                      true&inf_b_544=x' & inf_a_550=res&
                      {FLOW,(20,21)=__norm}[])
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure hdtl$node SUCCESS

Termination checking result:

Stop Omega... 34 invocations 
0 false contexts at: ()

Total verification time: 0.19 second(s)
	Time spent in main process: 0.18 second(s)
	Time spent in child processes: 0.01 second(s)

Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure hd$node... 
Procedure hd$node SUCCESS

Checking procedure tl$node... 
Procedure tl$node SUCCESS

Checking procedure hdtl$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[ inf_b_563::node<inf_a_569,inf_Anon_570>@inf_ann_568[Orig], x::node<inf_Anon_562,inf_b_563>@inf_ann_561[Orig]]
!!! Inferred Pure :[]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase emp&true&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 67::ref [x]
                                emp&true&{FLOW,(22,23)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase inf_b_563::node<inf_a_569,inf_Anon_570>@L[Orig] * 
                  x::node<inf_Anon_562,inf_b_563>@L[Orig]&MayLoop&
                  {FLOW,(1,25)=__flow}[]
                    EAssume 67::ref [x]
                      emp&inf_b_563=x' & inf_a_569=res&
                      {FLOW,(22,23)=__norm}[])
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure hdtl$node SUCCESS

Termination checking result:

Stop Omega... 33 invocations 
0 false contexts at: ()

Total verification time: 0.2 second(s)
	Time spent in main process: 0.19 second(s)
	Time spent in child processes: 0.01 second(s)

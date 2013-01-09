Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure hd$node... 
Procedure hd$node SUCCESS

Checking procedure tl$node... 
Procedure tl$node SUCCESS

Checking procedure hdtl$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[ inf_b_560::node<inf_a_566,inf_Anon_567>@inf_ann_565[Orig], x::node<inf_Anon_559,inf_b_560>@inf_ann_558[Orig]]
!!! Inferred Pure :[]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase emp&true&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 67::ref [x]
                                emp&true&{FLOW,(22,23)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase inf_b_560::node<inf_a_566,inf_Anon_567>@L[Orig] * 
                  x::node<inf_Anon_559,inf_b_560>@L[Orig]&MayLoop&
                  {FLOW,(1,25)=__flow}[]
                    EAssume 67::ref [x]
                      emp&inf_b_560=x' & inf_a_566=res&
                      {FLOW,(22,23)=__norm}[])
!!! NEW RELS:[]
!!! NEW ASSUME:[]
Procedure hdtl$node SUCCESS

Termination checking result:

Stop Omega... 37 invocations 
0 false contexts at: ()

Total verification time: 0.24 second(s)
	Time spent in main process: 0.22 second(s)
	Time spent in child processes: 0.02 second(s)


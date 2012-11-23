Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure hd0$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[ x::node<inf_val_14_532,inf_next_14_533>@inf_ann_531[Orig]]
!!! Inferred Pure :[]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                      EAssume 62::ref [x]
                        emp&true&{FLOW,(22,23)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase x::node<inf_val_14_532,inf_next_14_533>@L[Orig]&MayLoop&
                  {FLOW,(1,25)=__flow}[]
                    EAssume 62::ref [x]
                      emp&x'=x & inf_val_14_532=res&{FLOW,(22,23)=__norm}[])
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure hd0$node SUCCESS

Termination checking result:

Stop Omega... 29 invocations 
0 false contexts at: ()

Total verification time: 0.19 second(s)
	Time spent in main process: 0.18 second(s)
	Time spent in child processes: 0.01 second(s)


Processing file "t4-i.ss"
Parsing t4-i.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure hd0$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[ x::node<inf_val_14_498,inf_next_14_499>@inf_ann_497[Orig]]
!!! Inferred Pure :[]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase true&MayLoop&{FLOW,(1,23)=__flow}
                      EAssume 1::ref [x]
                        true&true&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase x::node<inf_val_14_498,inf_next_14_499>@L[Orig]&MayLoop&
                  {FLOW,(1,23)=__flow}
                    EAssume 1::ref [x]
                      true&x'=x & inf_val_14_498=res&{FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure hd0$node SUCCESS

Termination checking result:

Stop Omega... 36 invocations 
0 false contexts at: ()

Total verification time: 0.05 second(s)
	Time spent in main process: 0.04 second(s)
	Time spent in child processes: 0.01 second(s)

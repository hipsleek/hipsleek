
Processing file "t6-i.ss"
Parsing t6-i.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure hd$node... 
Procedure hd$node SUCCESS

Checking procedure tl$node... 
Procedure tl$node SUCCESS

Checking procedure hdtl$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[ inf_b_529::node<inf_a_535,inf_Anon_536>@inf_ann_534[Orig], x::node<inf_Anon_528,inf_b_529>@inf_ann_527[Orig]]
!!! Inferred Pure :[]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase true&true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 3::ref [x]
                                true&true&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase inf_b_529::node<inf_a_535,inf_Anon_536>@L[Orig] * 
                  x::node<inf_Anon_528,inf_b_529>@L[Orig]&MayLoop&
                  {FLOW,(1,23)=__flow}
                    EAssume 3::ref [x]
                      true&inf_b_529=x' & inf_a_535=res&{FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure hdtl$node SUCCESS

Termination checking result:

Stop Omega... 42 invocations 
0 false contexts at: ()

Total verification time: 0.05 second(s)
	Time spent in main process: 0.04 second(s)
	Time spent in child processes: 0.01 second(s)


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
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure hd$node SUCCESS

Checking procedure tl$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[ x::node<inf_val_38_542,inf_next_38_543>@inf_ann_541[Orig]]
!!! Inferred Pure :[]
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure tl$node SUCCESS

Checking procedure hdtl$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[ inf_inf_next_38_553::ll<inf_n_559>@inf_ann_558[Orig][LHSCase], x::node<inf_inf_val_38_552,inf_inf_next_38_553>@inf_ann_551[Orig]]
!!! Inferred Pure :[ inf_inf_next_38_553!=null, inf_ann_558<=0]
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure hdtl$node SUCCESS

Termination checking result:

Stop Omega... 108 invocations 
0 false contexts at: ()

Total verification time: 0.17 second(s)
	Time spent in main process: 0.15 second(s)
	Time spent in child processes: 0.02 second(s)

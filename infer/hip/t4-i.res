
Processing file "t4-i.ss"
Parsing t4-i.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure hd0$node... infer_heap_nodes
infer var: [x]
new infer var: [inf_ann_497,inf_val_14_498,inf_next_14_499,x]
OLD SPECS:  EInfer [x]
   EAssume 1::ref [x]
     true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase x::node<inf_val_14_498,inf_next_14_499>@inf_ann_497[Orig] &
       inf_ann_497<=2 & {FLOW,(1,23)=__flow}
         EAssume 1::ref [x]
           x::node<inf_val_14_498,inf_next_14_499>@inf_ann_497[Orig] &
           x=x' & res=inf_val_14_498 & inf_ann_497<=2 & {FLOW,(20,21)=__norm}

Procedure hd0$node SUCCESS
Stop Omega... 50 invocations 
0 false contexts at: ()

Total verification time: 0.18 second(s)
	Time spent in main process: 0.17 second(s)
	Time spent in child processes: 0.01 second(s)

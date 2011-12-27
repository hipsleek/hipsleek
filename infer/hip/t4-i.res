
Processing file "t4-i.ss"
Parsing t4-i.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure hd0$node... infer_heap_nodes
infer var: [x]
new infer var: [inf_ann_497,inf_val_14_498,inf_next_14_499,x]

Inferred Heap:[ x::node<inf_val_14_498,inf_next_14_499>@inf_ann_497[Orig]]
Inferred Pure:[]
OLD SPECS:  EInfer [x]
   EAssume 1::ref [x]
     true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase x::node<inf_val_14_498,inf_next_14_499>@L[Orig] & true &
       {FLOW,(1,23)=__flow}
         EAssume 1::ref [x]
           true & x=x' & res=inf_val_14_498 & {FLOW,(20,21)=__norm}
NEW RELS: []

Procedure hd0$node SUCCESS
Stop Omega... 37 invocations 
0 false contexts at: ()

Total verification time: 0.14 second(s)
	Time spent in main process: 0.13 second(s)
	Time spent in child processes: 0.01 second(s)

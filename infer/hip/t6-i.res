
Processing file "t6-i.ss"
Parsing t6-i.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure hd$node... 
Procedure hd$node SUCCESS
Checking procedure tl$node... 
Procedure tl$node SUCCESS
Checking procedure hdtl$node... infer_heap_nodes
infer var: [x]
new infer var: [inf_ann_527,inf_Anon_528,inf_b_529,x]
infer_heap_nodes
infer var: [inf_ann_527,inf_Anon_528,inf_b_529,x]
new infer var: [inf_ann_534,inf_a_535,inf_Anon_536,inf_ann_527,inf_Anon_528,inf_b_529,x]

Inferred Heap:[ x::node<inf_Anon_528,inf_b_529>@inf_ann_527[Orig], inf_b_529::node<inf_a_535,inf_Anon_536>@inf_ann_534[Orig]]
Inferred Pure:[]
OLD SPECS:  EInfer [x]
   EBase true & true & {FLOW,(20,21)=__norm}
           EAssume 3::ref [x]
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase x::node<inf_Anon_528,inf_b_529>@L[Orig] * 
       inf_b_529::node<inf_a_535,inf_Anon_536>@L[Orig] & true &
       {FLOW,(20,21)=__norm}
         EAssume 3::ref [x]
           true & inf_b_529=x' & inf_a_535=res & {FLOW,(20,21)=__norm}
NEW RELS: []

Procedure hdtl$node SUCCESS
Stop Omega... 45 invocations 
0 false contexts at: ()

Total verification time: 0.19 second(s)
	Time spent in main process: 0.18 second(s)
	Time spent in child processes: 0.01 second(s)

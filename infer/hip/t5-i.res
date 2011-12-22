
Processing file "t5-i.ss"
Parsing t5-i.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure hd$node... infer_heap_nodes
infer var: [x]
new infer var: [inf_ann_510,inf_val_16_511,inf_next_16_512,x]
OLD SPECS:  EInfer [x]
   EBase true & true & {FLOW,(20,21)=__norm}
           EAssume 1::
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase x::node<inf_val_16_511,inf_next_16_512>@inf_ann_510[Orig] &
       inf_ann_510<=2 & {FLOW,(20,21)=__norm}
         EAssume 1::
           x::node<inf_val_16_511,inf_next_16_512>@inf_ann_510[Orig] &
           res=inf_val_16_511 & inf_ann_510<=2 & {FLOW,(20,21)=__norm}

Procedure hd$node SUCCESS
Checking procedure tl$node... infer_heap_nodes
infer var: [x]
new infer var: [inf_ann_521,inf_val_33_522,inf_next_33_523,x]
OLD SPECS:  EInfer [x]
   EBase true & true & {FLOW,(20,21)=__norm}
           EAssume 4::
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase x::node<inf_val_33_522,inf_next_33_523>@inf_ann_521[Orig] &
       inf_ann_521<=2 & {FLOW,(20,21)=__norm}
         EAssume 4::
           x::node<inf_val_33_522,inf_next_33_523>@inf_ann_521[Orig] &
           res=inf_next_33_523 & inf_ann_521<=2 & {FLOW,(20,21)=__norm}

Procedure tl$node SUCCESS
Checking procedure hdtl$node... infer_heap_nodes
infer var: [x]
new infer var: [inf_ann_534,inf_inf_val_33_535,inf_inf_next_33_536,x]

Procedure Call:t5-i.ss:24: 6: 
Verification Context:(Line:22,Col:9)
Proving precondition in method tl$node for spec:
 EBase x'::node<inf_val_33_522,inf_next_33_523>@inf_ann_521[Orig] &
       inf_ann_521<=2 & {FLOW,(20,21)=__norm}
         EAssume 4::
           x'::node<inf_val_33_522,inf_next_33_523>@inf_ann_521[Orig] &
           res=inf_next_33_523 & inf_ann_521<=2 & {FLOW,(20,21)=__norm}
Current States: [ true & x'=x & {FLOW,(20,21)=__norm}
 es_infer_vars: [x]] has failed 

OLD SPECS:  EInfer [x]
   EBase true & true & {FLOW,(20,21)=__norm}
           EAssume 2::ref [x]
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EAssume 2::ref [x]
   true & true & {FLOW,(20,21)=__norm}

Procedure hdtl$node result FAIL-1
Stop Omega... 107 invocations 
0 false contexts at: ()

Total verification time: 0.25 second(s)
	Time spent in main process: 0.23 second(s)
	Time spent in child processes: 0.02 second(s)

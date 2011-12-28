
Processing file "t5-i.ss"
Parsing t5-i.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure hd$node... 
Inferred Heap:[]
Inferred Pure:[ x!=null]
OLD SPECS:  EInfer [x]
   EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase] & true &
         {FLOW,(20,21)=__norm}
           EAssume 1::
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase] & x!=null &
       {FLOW,(20,21)=__norm}
         EAssume 1::
           x::node<Anon_535,q_536>@M[Orig] * q_536::ll<flted_7_534>@M[Orig] &
           n=flted_7_534+1 & res=Anon_535 & 0<=n & {FLOW,(20,21)=__norm}
NEW RELS: []

Procedure hd$node SUCCESS
Checking procedure tl$node... infer_heap_nodes
infer var: [x]
new infer var: [inf_ann_541,inf_val_38_542,inf_next_38_543,x]

Inferred Heap:[ x::node<inf_val_38_542,inf_next_38_543>@inf_ann_541[Orig]]
Inferred Pure:[]
OLD SPECS:  EInfer [x]
   EBase true & true & {FLOW,(20,21)=__norm}
           EAssume 4::
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase x::node<inf_val_38_542,inf_next_38_543>@L[Orig] & true &
       {FLOW,(20,21)=__norm}
         EAssume 4::
           true & res=inf_next_38_543 & {FLOW,(20,21)=__norm}
NEW RELS: []

Procedure tl$node SUCCESS
Checking procedure hdtl$node... infer_heap_nodes
infer var: [x]
new infer var: [inf_ann_551,inf_inf_val_38_552,inf_inf_next_38_553,x]
infer_heap_nodes
infer var: [inf_ann_551,inf_inf_val_38_552,inf_inf_next_38_553,x]
new infer var: [inf_ann_558,inf_n_559,inf_ann_551,inf_inf_val_38_552,inf_inf_next_38_553,x]

Inferred Heap:[ x::node<inf_inf_val_38_552,inf_inf_next_38_553>@inf_ann_551[Orig], inf_inf_next_38_553::ll<inf_n_559>@inf_ann_558[Orig][LHSCase]]
Inferred Pure:[ inf_ann_558<=0 & x!=null, inf_inf_next_38_553!=null]
OLD SPECS:  EInfer [x]
   EBase true & true & {FLOW,(20,21)=__norm}
           EAssume 2::ref [x]
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase x::node<inf_inf_val_38_552,inf_inf_next_38_553>@L[Orig] * 
       inf_inf_next_38_553::ll<inf_n_559>@L[Orig][LHSCase] &
       inf_inf_next_38_553!=null & {FLOW,(20,21)=__norm}
         EAssume 2::ref [x]
           x'::node<Anon_535,q_536>@M[Orig] * 
           q_536::ll<flted_7_534>@M[Orig] & inf_ann_558<=0 & 
           inf_inf_next_38_553=x' & flted_7_534=inf_n_559 - 1 & 
           res=Anon_535 & x!=null & x'!=null & 0<=inf_n_559 & 0<=inf_n_559 &
           {FLOW,(20,21)=__norm}
NEW RELS: []

Procedure hdtl$node SUCCESS
Stop Omega... 95 invocations 
0 false contexts at: ()

Total verification time: 0.25 second(s)
	Time spent in main process: 0.22 second(s)
	Time spent in child processes: 0.03 second(s)

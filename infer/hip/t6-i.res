
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
infer var: [inf_Anon_528,inf_b_529,x]
new infer var: [inf_ann_534,inf_a_535,inf_Anon_536,inf_Anon_528,inf_b_529,x]
OLD SPECS:  EInfer [x]
   EBase true & true & {FLOW,(20,21)=__norm}
           EAssume 3::ref [x]
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase x::node<inf_Anon_528,inf_b_529>@inf_ann_527[Orig] * 
       inf_b_529::node<inf_a_535,inf_Anon_536>@inf_ann_534[Orig] &
       inf_ann_534<=2 & {FLOW,(20,21)=__norm}
         EAssume 3::ref [x]
           x::node<inf_Anon_528,inf_b_529>@inf_ann_527[Orig] * 
           inf_b_529::node<inf_a_535,inf_Anon_536>@inf_ann_534[Orig] &
           x'=inf_b_529 & res=inf_a_535 & inf_ann_527<=2 & inf_ann_534<=2 &
           {FLOW,(20,21)=__norm}

Procedure Call:t6-i.ss:26: 6: 
Verification Context:(Line:0,Col:0)
Proving precondition in method tl$node for spec:
 EBase exists (Expl)(Impl)[Anon_12; b](ex)x'::node<Anon_12,b>@L[Orig] &
       true & {FLOW,(20,21)=__norm}
         EAssume 2::
           true & res=b & {FLOW,(20,21)=__norm}
Current States: [ x::node<inf_Anon_528,inf_b_529>@inf_ann_527[Orig] * inf_b_529::node<inf_a_535,inf_Anon_536>@inf_ann_534[Orig] & x'=x & inf_ann_534<=2 & {FLOW,(20,21)=__norm}] has failed 


Procedure hdtl$node SUCCESS
Stop Omega... 81 invocations 
0 false contexts at: ()

Total verification time: 0.27 second(s)
	Time spent in main process: 0.25 second(s)
	Time spent in child processes: 0.02 second(s)

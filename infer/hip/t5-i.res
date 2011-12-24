
Processing file "t5-i.ss"
Parsing t5-i.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure hd$node... OLD SPECS:  EInfer [x]
   EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase] & true &
         {FLOW,(20,21)=__norm}
           EAssume 1::
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase] & x!=null &
       {FLOW,(20,21)=__norm}
         EAssume 1::
           x::node<Anon_535,q_536>@M[Orig] * q_536::ll<flted_7_534>@M[Orig] &
           n=flted_7_534+1 & res=Anon_535 & 0<=n & {FLOW,(20,21)=__norm}

Procedure hd$node SUCCESS
Checking procedure tl$node... infer_heap_nodes
infer var: [x]
new infer var: [inf_ann_561,inf_val_36_562,inf_next_36_563,x]
OLD SPECS:  EInfer [x]
   EBase true & true & {FLOW,(20,21)=__norm}
           EAssume 4::
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase x::node<inf_val_36_562,inf_next_36_563>@inf_ann_561[Orig] & true &
       {FLOW,(20,21)=__norm}
         EAssume 4::
           x::node<inf_val_36_562,inf_next_36_563>@inf_ann_561[Orig] &
           res=inf_next_36_563 & {FLOW,(20,21)=__norm}

Procedure tl$node SUCCESS
Checking procedure hdtl$node... infer_heap_nodes
infer var: [x]
new infer var: [inf_ann_574,inf_inf_val_36_575,inf_inf_next_36_576,x]

Procedure Call:t5-i.ss:27: 6: 
Verification Context:(Line:25,Col:9)
Proving precondition in method tl$node for spec:
 EBase x'::node<inf_val_36_562,inf_next_36_563>@inf_ann_561[Orig] & true &
       {FLOW,(20,21)=__norm}
         EAssume 4::
           x'::node<inf_val_36_562,inf_next_36_563>@inf_ann_561[Orig] &
           res=inf_next_36_563 & {FLOW,(20,21)=__norm}
Current States: [ true & x'=x & {FLOW,(20,21)=__norm}
 es_infer_vars: [x]] has failed 

OLD SPECS:  EInfer [x]
   EBase true & true & {FLOW,(20,21)=__norm}
           EAssume 2::ref [x]
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EAssume 2::ref [x]
   true & true & {FLOW,(20,21)=__norm}

Procedure hdtl$node result FAIL-1
Stop Omega... 104 invocations 
0 false contexts at: ()

Total verification time: 0.24 second(s)
	Time spent in main process: 0.22 second(s)
	Time spent in child processes: 0.02 second(s)

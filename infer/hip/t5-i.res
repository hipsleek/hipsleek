
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
new infer var: [inf_ann_561,inf_val_38_562,inf_next_38_563,x]
OLD SPECS:  EInfer [x]
   EBase true & true & {FLOW,(20,21)=__norm}
           EAssume 4::
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase x::node<inf_val_38_562,inf_next_38_563>@L[Orig] & true &
       {FLOW,(20,21)=__norm}
         EAssume 4::
           true & res=inf_next_38_563 & {FLOW,(20,21)=__norm}

Procedure tl$node SUCCESS
Checking procedure hdtl$node... infer_heap_nodes
infer var: [x]
new infer var: [inf_ann_576,inf_inf_val_38_577,inf_inf_next_38_578,x]
infer_heap_nodes
infer var: [inf_ann_576,inf_inf_val_38_577,inf_inf_next_38_578,x]
new infer var: [inf_ann_583,inf_n_584,inf_ann_576,inf_inf_val_38_577,inf_inf_next_38_578,x]
OLD SPECS:  EInfer [x]
   EBase true & true & {FLOW,(20,21)=__norm}
           EAssume 2::ref [x]
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase x::node<inf_inf_val_38_577,inf_inf_next_38_578>@L[Orig] * 
       inf_inf_next_38_578::ll<inf_n_584>@L[Orig][LHSCase] &
       inf_inf_next_38_578!=null & {FLOW,(20,21)=__norm}
         EAssume 2::ref [x]
           x'::node<Anon_535,q_536>@M[Orig] * 
           q_536::ll<flted_7_534>@M[Orig] & inf_ann_583<=0 & res=Anon_535 & 
           inf_inf_next_38_578=x' & flted_7_534=inf_n_584 - 1 & x!=null & 
           x'!=null & 0<=inf_n_584 & 0<=inf_n_584 & {FLOW,(20,21)=__norm}

Procedure Call:t5-i.ss:30: 9: 
Verification Context:(Line:0,Col:0)
Proving precondition in method hd$node for spec:
 EBase exists (Expl)(Impl)[n](ex)x'::ll<n>@M[Orig][LHSCase] & x'!=null &
       {FLOW,(20,21)=__norm}
         EAssume 1::
           x'::node<Anon_535,q_536>@M[Orig] * 
           q_536::ll<flted_7_534>@M[Orig] & n=flted_7_534+1 & res=Anon_535 & 
           0<=n & {FLOW,(20,21)=__norm}
Current States: [ x::node<inf_inf_val_38_577,inf_inf_next_38_578>@L[Orig] * inf_inf_next_38_578::ll<inf_n_584>@L[Orig][LHSCase] & inf_inf_next_38_578!=null & inf_val_38_587=inf_inf_val_38_577 & inf_next_38_563=inf_inf_next_38_578 & x'=inf_next_38_563 & {FLOW,(20,21)=__norm}] has failed 


Procedure hdtl$node SUCCESS
Stop Omega... 142 invocations 
0 false contexts at: ()

Total verification time: 0.964059 second(s)
	Time spent in main process: 0.740046 second(s)
	Time spent in child processes: 0.224013 second(s)

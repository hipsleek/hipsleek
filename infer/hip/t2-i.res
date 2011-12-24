
Processing file "t2-i.ss"
Parsing t2-i.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure hd0$node... infer_heap_nodes
infer var: [x]
new infer var: [inf_ann_542,inf_val_20_543,inf_next_20_544,x]
infer_heap_nodes
infer var: [inf_ann_542,inf_val_20_543,inf_next_20_544,x]
new infer var: [inf_ann_549,inf_val_21_550,inf_next_21_551,inf_ann_542,inf_val_20_543,inf_next_20_544,x]
OLD SPECS:  EInfer [x]
   EBase true & true & {FLOW,(20,21)=__norm}
           EAssume 1::ref [x]
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase x::node<inf_val_20_543,inf_next_20_544>@L[Orig] * 
       inf_next_20_544::node<inf_val_21_550,inf_next_21_551>@L[Orig] & true &
       {FLOW,(20,21)=__norm}
         EAssume 1::ref [x]
           true & inf_next_20_544=x' & res=inf_val_21_550 &
           {FLOW,(20,21)=__norm}

Procedure hd0$node SUCCESS
Checking procedure hd1$node... infer_heap_nodes
infer var: [x]
new infer var: [inf_ann_564,inf_val_33_565,inf_next_33_566,x]
OLD SPECS:  EInfer [x]
   EBase true & true & {FLOW,(20,21)=__norm}
           EAssume 3::
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase x::node<inf_val_33_565,inf_next_33_566>@L[Orig] & true &
       {FLOW,(20,21)=__norm}
         EAssume 3::
           true & res=inf_val_33_565 & {FLOW,(20,21)=__norm}

Procedure hd1$node SUCCESS
Checking procedure hd2$node... OLD SPECS:  EInfer [x]
   EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase] & true &
         {FLOW,(20,21)=__norm}
           EAssume 4::
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase] & x!=null &
       {FLOW,(20,21)=__norm}
         EAssume 4::
           x::node<Anon_587,q_588>@M[Orig] * q_588::ll<flted_8_586>@M[Orig] &
           n=flted_8_586+1 & res=Anon_587 & 0<=n & {FLOW,(20,21)=__norm}

Procedure hd2$node SUCCESS
Checking procedure hd3$node... OLD SPECS:  EInfer [n]
   EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase] & true &
         {FLOW,(20,21)=__norm}
           EAssume 5::
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase] & n!=0 &
       {FLOW,(20,21)=__norm}
         EAssume 5::
           x::node<Anon_625,q_626>@M[Orig] * q_626::ll<flted_8_624>@M[Orig] &
           n=flted_8_624+1 & res=Anon_625 & 0<=n & {FLOW,(20,21)=__norm}

Procedure hd3$node SUCCESS
Checking procedure hd4$node... 
( ) :t2-i.ss:71: 9: bind: node  x'::node<val_71_501',next_71_502'>@L[Orig] cannot be derived from context


(Cause of Bind Failure):t2-i.ss:71: 9:  List of Failesc Context: [FEC(1, 0, 0 )]
Failed States:
[
 Label: 
 State:
        
         fe_kind: MUST
         fe_name: separation entailment
         fe_locs: {
                   fc_message: 15.1 x'=null & x'=x |-  x'!=null (must-bug).
                   fc_current_lhs_flow: {FLOW,(1,5)=__Error}}
       FAIL_OR 
        
         fe_kind: Valid
         fe_name: 
         fe_locs: Failure_Valid
       
 ]
OLD SPECS:  EInfer @post []
   EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase] & true &
         {FLOW,(20,21)=__norm}
           EAssume 6::
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase] & true &
       {FLOW,(20,21)=__norm}
         EAssume 6::
           true & 0<=n & {FLOW,(20,21)=__norm}

Procedure hd4$node result FAIL-1
Stop Omega... 122 invocations 
0 false contexts at: ()

Total verification time: 1.080065 second(s)
	Time spent in main process: 0.932057 second(s)
	Time spent in child processes: 0.148008 second(s)

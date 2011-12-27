
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

Inferred Heap:[ x::node<inf_val_20_543,inf_next_20_544>@inf_ann_542[Orig], inf_next_20_544::node<inf_val_21_550,inf_next_21_551>@inf_ann_549[Orig]]
Inferred Pure:[]
OLD SPECS:  EInfer [x]
   EBase true & true & {FLOW,(20,21)=__norm}
           EAssume 1::ref [x]
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase x::node<inf_val_20_543,inf_next_20_544>@L[Orig] * 
       inf_next_20_544::node<inf_val_21_550,inf_next_21_551>@L[Orig] & true &
       {FLOW,(20,21)=__norm}
         EAssume 1::ref [x]
           true & x'=inf_next_20_544 & inf_val_21_550=res &
           {FLOW,(20,21)=__norm}
NEW RELS: []

Procedure hd0$node SUCCESS
Checking procedure hd1$node... infer_heap_nodes
infer var: [x]
new infer var: [inf_ann_556,inf_val_33_557,inf_next_33_558,x]

Inferred Heap:[ x::node<inf_val_33_557,inf_next_33_558>@inf_ann_556[Orig]]
Inferred Pure:[]
OLD SPECS:  EInfer [x]
   EBase true & true & {FLOW,(20,21)=__norm}
           EAssume 3::
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase x::node<inf_val_33_557,inf_next_33_558>@L[Orig] & true &
       {FLOW,(20,21)=__norm}
         EAssume 3::
           true & inf_val_33_557=res & {FLOW,(20,21)=__norm}
NEW RELS: []

Procedure hd1$node SUCCESS
Checking procedure hd2$node... 
Inferred Heap:[]
Inferred Pure:[ x!=null]
OLD SPECS:  EInfer [x]
   EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase] & true &
         {FLOW,(20,21)=__norm}
           EAssume 4::
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase] & x!=null &
       {FLOW,(20,21)=__norm}
         EAssume 4::
           x::node<Anon_575,q_576>@M[Orig] * q_576::ll<flted_8_574>@M[Orig] &
           flted_8_574=n - 1 & Anon_575=res & 0<=n & {FLOW,(20,21)=__norm}
NEW RELS: []

Procedure hd2$node SUCCESS
Checking procedure hd3$node... 
Inferred Heap:[]
Inferred Pure:[ n!=0]
OLD SPECS:  EInfer [n]
   EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase] & true &
         {FLOW,(20,21)=__norm}
           EAssume 5::
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase] & n!=0 &
       {FLOW,(20,21)=__norm}
         EAssume 5::
           x::node<Anon_593,q_594>@M[Orig] * q_594::ll<flted_8_592>@M[Orig] &
           flted_8_592=n - 1 & Anon_593=res & 0<=n & {FLOW,(20,21)=__norm}
NEW RELS: []

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
NEW RELS: []

Procedure hd4$node result FAIL-1
Stop Omega... 83 invocations 
0 false contexts at: ()

Total verification time: 0.25 second(s)
	Time spent in main process: 0.23 second(s)
	Time spent in child processes: 0.02 second(s)

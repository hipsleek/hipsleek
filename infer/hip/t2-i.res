
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
infer var: [inf_val_20_543,inf_next_20_544,x]
new infer var: [inf_ann_549,inf_val_21_550,inf_next_21_551,inf_val_20_543,inf_next_20_544,x]
OLD SPECS:  EInfer [x]
   EBase true & true & {FLOW,(20,21)=__norm}
           EAssume 1::ref [x]
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase x::node<inf_val_20_543,inf_next_20_544>@inf_ann_542[Orig] * 
       inf_next_20_544::node<inf_val_21_550,inf_next_21_551>@inf_ann_549[Orig] &
       inf_ann_549<=2 & {FLOW,(20,21)=__norm}
         EAssume 1::ref [x]
           x::node<inf_val_20_543,inf_next_20_544>@inf_ann_542[Orig] * 
           inf_next_20_544::node<inf_val_21_550,inf_next_21_551>@inf_ann_549[Orig] &
           inf_next_20_544=x' & res=inf_val_21_550 & inf_ann_542<=2 & 
           inf_ann_549<=2 & {FLOW,(20,21)=__norm}

( ) :t2-i.ss:20: 6: bind: node  x'::node<val_20_527',next_20_528'>@L[Orig] cannot be derived from context


(Cause of Bind Failure):t2-i.ss:20: 6:  List of Failesc Context: [FEC(1, 0, 0 )]
Failed States:
[
 Label: 
 State:
        fe_kind: MAY
        fe_name: logical bug
        fe_locs: {
                  fc_message: use different strategies in proof searching (slicing)
                  fc_current_lhs_flow: {FLOW,(1,23)=__flow}}
 ]

Procedure hd0$node SUCCESS
Checking procedure hd1$node... infer_heap_nodes
infer var: [x]
new infer var: [inf_ann_561,inf_val_33_562,inf_next_33_563,x]
OLD SPECS:  EInfer [x]
   EBase true & true & {FLOW,(20,21)=__norm}
           EAssume 3::
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase x::node<inf_val_33_562,inf_next_33_563>@inf_ann_561[Orig] &
       inf_ann_561<=2 & {FLOW,(20,21)=__norm}
         EAssume 3::
           x::node<inf_val_33_562,inf_next_33_563>@inf_ann_561[Orig] &
           res=inf_val_33_562 & inf_ann_561<=2 & {FLOW,(20,21)=__norm}

Procedure hd1$node SUCCESS
Checking procedure hd2$node... OLD SPECS:  EInfer [x]
   EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase] & true &
         {FLOW,(20,21)=__norm}
           EAssume 4::
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase] & x!=null &
       {FLOW,(20,21)=__norm}
         EAssume 4::
           x::node<Anon_584,q_585>@M[Orig] * q_585::ll<flted_8_583>@M[Orig] &
           n=flted_8_583+1 & res=Anon_584 & 0<=n & {FLOW,(20,21)=__norm}

Procedure hd2$node SUCCESS
Checking procedure hd3$node... OLD SPECS:  EInfer [n]
   EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase] & true &
         {FLOW,(20,21)=__norm}
           EAssume 5::
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase] & n!=0 &
       {FLOW,(20,21)=__norm}
         EAssume 5::
           x::node<Anon_622,q_623>@M[Orig] * q_623::ll<flted_8_621>@M[Orig] &
           n=flted_8_621+1 & res=Anon_622 & 0<=n & {FLOW,(20,21)=__norm}

Procedure hd3$node SUCCESS
Checking procedure hd4$node... 
( ) :t2-i.ss:70: 9: bind: node  x'::node<val_70_501',next_70_502'>@L[Orig] cannot be derived from context


(Cause of Bind Failure):t2-i.ss:70: 9:  List of Failesc Context: [FEC(1, 0, 0 )]
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
Stop Omega... 142 invocations 
0 false contexts at: ()

Total verification time: 0.4 second(s)
	Time spent in main process: 0.37 second(s)
	Time spent in child processes: 0.03 second(s)

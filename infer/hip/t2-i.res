
Processing file "t2-i.ss"
Parsing t2-i.ss ...
Parsing /home2/loris/hg/sl_infer/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
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

Procedure hd4$node result FAIL-1
Checking procedure hd3$node... 
Inferred Heap:[]
Inferred Pure:[ n!=0]
Pre Vars :[x,n]
Exists Post Vars :[v_int_58_510']
Residual Post :  x::node<Anon_573,q_574>@M[Orig] * q_574::ll<flted_8_572>@M[Orig] &
n=flted_8_572+1 & res=Anon_573 & {FLOW,(20,21)=__norm}
OLD SPECS:  EInfer [n]
   EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase] & true &
         {FLOW,(20,21)=__norm}
           EAssume 5::
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase] & n!=0 &
       {FLOW,(20,21)=__norm}
         EAssume 5::
           x::node<Anon_573,q_574>@M[Orig] * q_574::ll<flted_8_572>@M[Orig] &
           n=flted_8_572+1 & res=Anon_573 & 0<=n & {FLOW,(20,21)=__norm}

Procedure hd3$node SUCCESS
Checking procedure hd2$node... 
Inferred Heap:[]
Inferred Pure:[ x!=null]
Pre Vars :[n,x]
Exists Post Vars :[v_int_46_517']
Residual Post :  x::node<Anon_593,q_594>@M[Orig] * q_594::ll<flted_8_592>@M[Orig] &
n=flted_8_592+1 & res=Anon_593 & {FLOW,(20,21)=__norm}
OLD SPECS:  EInfer [x]
   EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase] & true &
         {FLOW,(20,21)=__norm}
           EAssume 4::
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase] & x!=null &
       {FLOW,(20,21)=__norm}
         EAssume 4::
           x::node<Anon_593,q_594>@M[Orig] * q_594::ll<flted_8_592>@M[Orig] &
           n=flted_8_592+1 & res=Anon_593 & 0<=n & {FLOW,(20,21)=__norm}

Procedure hd2$node SUCCESS
Checking procedure hd1$node... 
Inferred Heap:[ x::node<inf_val_33_599,inf_next_33_600>@L[Orig]]
Inferred Pure:[]
Pre Vars :[inf_val_33_599,inf_next_33_600,x]
Exists Post Vars :[v_int_33_523']
Residual Post :  true & res=inf_val_33_599 & {FLOW,(20,21)=__norm}
OLD SPECS:  EInfer [x]
   EBase true & true & {FLOW,(20,21)=__norm}
           EAssume 3::
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase x::node<inf_val_33_599,inf_next_33_600>@L[Orig] & true &
       {FLOW,(20,21)=__norm}
         EAssume 3::
           true & res=inf_val_33_599 & {FLOW,(20,21)=__norm}

Procedure hd1$node SUCCESS
Checking procedure hd0$node... 
Inferred Heap:[ x::node<inf_val_20_605,inf_next_20_606>@L[Orig], inf_next_20_606::node<inf_val_21_611,inf_next_21_612>@L[Orig]]
Inferred Pure:[]
Pre Vars :[inf_val_21_611,inf_next_21_612,inf_val_20_605,inf_next_20_606,x]
Exists Post Vars :[v_int_21_531']
Residual Post :  true & inf_next_20_606=x' & res=inf_val_21_611 & {FLOW,(20,21)=__norm}
OLD SPECS:  EInfer [x]
   EBase true & true & {FLOW,(20,21)=__norm}
           EAssume 1::ref [x]
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase x::node<inf_val_20_605,inf_next_20_606>@L[Orig] * 
       inf_next_20_606::node<inf_val_21_611,inf_next_21_612>@L[Orig] & true &
       {FLOW,(20,21)=__norm}
         EAssume 1::ref [x]
           true & inf_next_20_606=x' & res=inf_val_21_611 &
           {FLOW,(20,21)=__norm}

Procedure hd0$node SUCCESS
Stop Omega... 73 invocations 
0 false contexts at: ()

Total verification time: 0.400024 second(s)
	Time spent in main process: 0.208012 second(s)
	Time spent in child processes: 0.192012 second(s)

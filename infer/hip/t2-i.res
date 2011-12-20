
Processing file "t2-i.ss"
Parsing t2-i.ss ...
Parsing /home/thaitm/hg-repository/new/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure hd0$node... 
Inferred Heap:[ x::node<inf_val_20_542,inf_next_20_543>@L[Orig], inf_next_20_543::node<inf_val_21_548,inf_next_21_549>@L[Orig]]
Inferred Pure:[]
Pre Vars :[inf_val_21_548,inf_next_21_549,inf_val_20_542,inf_next_20_543,x]
Exists Post Vars :[v_int_21_531']
Initial Residual Post : [ true & x'=inf_next_20_543 & v_int_21_531'=inf_val_21_548 & 
res=v_int_21_531' & {FLOW,(20,21)=__norm}]
Final Residual Post :  true & inf_next_20_543=x' & res=inf_val_21_548 & {FLOW,(20,21)=__norm}
OLD SPECS:  EInfer [x]
   EBase true & true & {FLOW,(20,21)=__norm}
           EAssume 1::ref [x]
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase x::node<inf_val_20_542,inf_next_20_543>@L[Orig] * 
       inf_next_20_543::node<inf_val_21_548,inf_next_21_549>@L[Orig] & true &
       {FLOW,(20,21)=__norm}
         EAssume 1::ref [x]
           true & inf_next_20_543=x' & res=inf_val_21_548 &
           {FLOW,(20,21)=__norm}

Procedure hd0$node SUCCESS
Checking procedure hd1$node... 
Inferred Heap:[ x::node<inf_val_33_554,inf_next_33_555>@L[Orig]]
Inferred Pure:[]
Pre Vars :[inf_val_33_554,inf_next_33_555,x]
Exists Post Vars :[v_int_33_523']
Initial Residual Post : [ true & v_int_33_523'=inf_val_33_554 & res=v_int_33_523' &
{FLOW,(20,21)=__norm}]
Final Residual Post :  true & res=inf_val_33_554 & {FLOW,(20,21)=__norm}
OLD SPECS:  EInfer [x]
   EBase true & true & {FLOW,(20,21)=__norm}
           EAssume 3::
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase x::node<inf_val_33_554,inf_next_33_555>@L[Orig] & true &
       {FLOW,(20,21)=__norm}
         EAssume 3::
           true & res=inf_val_33_554 & {FLOW,(20,21)=__norm}

Procedure hd1$node SUCCESS
Checking procedure hd2$node... 
Inferred Heap:[]
Inferred Pure:[ x!=null]
Pre Vars :[n,x]
Exists Post Vars :[v_int_46_517']
Initial Residual Post : [ x::node<Anon_574,q_575>@M[Orig] * q_575::ll<flted_8_573>@M[Orig] &
flted_8_573+1=n & v_int_46_517'=Anon_574 & res=v_int_46_517' &
{FLOW,(20,21)=__norm}]
Final Residual Post :  x::node<Anon_574,q_575>@M[Orig] * q_575::ll<flted_8_573>@M[Orig] &
n=flted_8_573+1 & res=Anon_574 & {FLOW,(20,21)=__norm}
OLD SPECS:  EInfer [x]
   EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase] & true &
         {FLOW,(20,21)=__norm}
           EAssume 4::
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase] & x!=null &
       {FLOW,(20,21)=__norm}
         EAssume 4::
           x::node<Anon_574,q_575>@M[Orig] * q_575::ll<flted_8_573>@M[Orig] &
           n=flted_8_573+1 & res=Anon_574 & 0<=n & {FLOW,(20,21)=__norm}

Procedure hd2$node SUCCESS
Checking procedure hd3$node... 
Inferred Heap:[]
Inferred Pure:[ n!=0]
Pre Vars :[x,n]
Exists Post Vars :[v_int_58_510']
Initial Residual Post : [ x::node<Anon_594,q_595>@M[Orig] * q_595::ll<flted_8_593>@M[Orig] &
flted_8_593+1=n & v_int_58_510'=Anon_594 & res=v_int_58_510' &
{FLOW,(20,21)=__norm}]
Final Residual Post :  x::node<Anon_594,q_595>@M[Orig] * q_595::ll<flted_8_593>@M[Orig] &
n=flted_8_593+1 & res=Anon_594 & {FLOW,(20,21)=__norm}
OLD SPECS:  EInfer [n]
   EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase] & true &
         {FLOW,(20,21)=__norm}
           EAssume 5::
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase] & n!=0 &
       {FLOW,(20,21)=__norm}
         EAssume 5::
           x::node<Anon_594,q_595>@M[Orig] * q_595::ll<flted_8_593>@M[Orig] &
           n=flted_8_593+1 & res=Anon_594 & 0<=n & {FLOW,(20,21)=__norm}

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
Stop Omega... 75 invocations 
0 false contexts at: ()

Total verification time: 0.11 second(s)
	Time spent in main process: 0.08 second(s)
	Time spent in child processes: 0.03 second(s)

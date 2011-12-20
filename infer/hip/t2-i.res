
Processing file "t2-i.ss"
Parsing t2-i.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure hd0$node... OLD SPECS:  EInfer [x]
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
Checking procedure hd1$node... OLD SPECS:  EInfer [x]
   EBase true & true & {FLOW,(20,21)=__norm}
           EAssume 3::
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase x::node<inf_val_33_554,inf_next_33_555>@L[Orig] & true &
       {FLOW,(20,21)=__norm}
         EAssume 3::
           true & res=inf_val_33_554 & {FLOW,(20,21)=__norm}

Procedure hd1$node SUCCESS
Checking procedure hd2$node... OLD SPECS:  EInfer [x]
   EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase] & true &
         {FLOW,(20,21)=__norm}
           EAssume 4::
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase] & x!=null &
       {FLOW,(20,21)=__norm}
         EAssume 4::
           x::node<Anon_572,q_573>@M[Orig] * q_573::ll<flted_8_571>@M[Orig] &
           n=flted_8_571+1 & res=Anon_572 & 0<=n & {FLOW,(20,21)=__norm}

Procedure hd2$node SUCCESS
Checking procedure hd3$node... OLD SPECS:  EInfer [n]
   EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase] & true &
         {FLOW,(20,21)=__norm}
           EAssume 5::
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase] & n!=0 &
       {FLOW,(20,21)=__norm}
         EAssume 5::
           x::node<Anon_590,q_591>@M[Orig] * q_591::ll<flted_8_589>@M[Orig] &
           n=flted_8_589+1 & res=Anon_590 & 0<=n & {FLOW,(20,21)=__norm}

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
Stop Omega... 72 invocations 
0 false contexts at: ()

Total verification time: 0.792048 second(s)
	Time spent in main process: 0.624039 second(s)
	Time spent in child processes: 0.168009 second(s)


Processing file "t2-i.ss"
Parsing t2-i.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure hd4$node... 
( ) :t2-i.ss:57: 9: bind: node  x'::node<val_57_500',next_57_501'>@L[Orig] cannot be derived from context


(Cause of Bind Failure):t2-i.ss:57: 9:  List of Failesc Context: [FEC(1, 0, 0 )]
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
Residual Post : [ x::node<Anon_564,q_565>@M[Orig] * q_565::ll<flted_8_563>@M[Orig] &
flted_8_563+1=n & v_int_45_509'=Anon_564 & res=v_int_45_509' &
{FLOW,(20,21)=__norm}]

Procedure hd3$node SUCCESS
Checking procedure hd2$node... 
Inferred Heap:[]
Inferred Pure:[ x!=null]
Residual Post : [ x::node<Anon_584,q_585>@M[Orig] * q_585::ll<flted_8_583>@M[Orig] &
flted_8_583+1=n & v_int_33_516'=Anon_584 & res=v_int_33_516' &
{FLOW,(20,21)=__norm}]

Procedure hd2$node SUCCESS
Checking procedure hd1$node... 
Inferred Heap:[ x'::node<inf_val_20_590,inf_next_20_591>@L[Orig]]
Inferred Pure:[]
Residual Post : [ x::node<inf_val_20_590,inf_next_20_591>@L[Orig] &
v_int_20_522'=inf_val_20_590 & res=v_int_20_522' & {FLOW,(20,21)=__norm}]

Procedure hd1$node SUCCESS
Stop Omega... 65 invocations 
0 false contexts at: ()

Total verification time: 0.848051 second(s)
	Time spent in main process: 0.680041 second(s)
	Time spent in child processes: 0.16801 second(s)

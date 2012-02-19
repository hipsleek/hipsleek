
Processing file "bst-insert-b.ss"
Parsing bst-insert-b.ss ...
Parsing /home2/loris/hg/sl_infer/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure insert$node2~int... 
( [(64::,1 ); (64::,1 ); (63::,1 ); (63::,1 )]) :bst-insert-b.ss:24: 10: Postcondition cannot be derived from context


(Cause of PostCond Failure):bst-insert-b.ss:24: 10:  List of Partial Context: [PC(1, 0)]
Failed States:
[
 Label: [(64::,1 ); (64::,1 ); (63::,1 ); (63::,1 )]
 State:
        
         fe_kind: MUST
         fe_name: logical bug
         fe_locs: {
                   fc_message: 
                    (failure_code=213)  x!=null & x!=null & x!=null & v_node2_51_556'=x & res=v_node2_51_556' |-  res=null (must-bug).
                   fc_current_lhs_flow: {FLOW,(1,5)=__Error}}
       FAIL_UNION 
        
         fe_kind: MAY
         fe_name: logical bug
         fe_locs: {
                   fc_message: 
                    (failure_code=213)  lg_604=lg & lg_658=lg_604 & qs_606<=lg_604 & v_607<=qs_606 & sm_603=sm & 
v_607<a & v_607<a & sm_657=qs_606 & v_node2_48_760!=null & ma_686=max(lg_658,
a) & sm_657<=lg_658 & p_762=p_608 & q_763=v_node2_48_760 & pl_605<=v_607 & 
A(mi_685,sm_657,a) & v_761=v_607 & (v_node2_48_760=null & mi_685<=ma_686 | 
v_node2_48_760!=null & mi_685<=ma_686) & (p_608=null & sm_603<=pl_605 | 
p_608!=null & sm_603<=pl_605) |-  v_761<=mi_685 (may-bug).
                   fc_current_lhs_flow: {FLOW,(1,23)=__flow}}
       FAIL_UNION 
         Trivial fail : MUSTno lemma found in both LHS and RHS nodes (do coercion)
       
 ]
Successful States:


Context of Verification Failure: File "bst-insert-b.ss",Line:24,Col:10
Last Proving Location: File "bst-insert-b.ss",Line:48,Col:3

ERROR: at bst-insert-b.ss_24_10 
Message: Post condition cannot be derived by the system.
 
Procedure insert$node2~int FAIL-2

Exception Failure("Post condition cannot be derived by the system.") Occurred!

Error(s) detected when checking procedure insert$node2~int

Termination checking result:

Stop Omega... 270 invocations 
0 false contexts at: ()

Total verification time: 4.800299 second(s)
	Time spent in main process: 0.108006 second(s)
	Time spent in child processes: 4.692293 second(s)

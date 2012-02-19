
Processing file "bst-insert.ss"
Parsing bst-insert.ss ...
Parsing /home2/loris/hg/sl_infer/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure insert$node2~int... 
( [(64::,0 ); (64::,0 ); (63::,1 ); (63::,1 )]) :bst-insert.ss:24: 10: Postcondition cannot be derived from context


(Cause of PostCond Failure):bst-insert.ss:24: 10:  List of Partial Context: [PC(2, 0)]
Failed States:
[
 Label: [(64::,0 ); (64::,0 ); (63::,1 ); (63::,1 )]
 State:
        
         fe_kind: MUST
         fe_name: logical bug
         fe_locs: {
                   fc_message: 
                    (failure_code=213)  x!=null & x!=null & x!=null & v_node2_51_555'=x & res=v_node2_51_555' |-  res=null (must-bug).
                   fc_current_lhs_flow: {FLOW,(1,5)=__Error}}
       FAIL_UNION 
        
         fe_kind: MAY
         fe_name: logical bug
         fe_locs: {
                   fc_message: 
                    (failure_code=213)  sm_602=sm & sm_602<=pl_604 & pl_604<=v_606 & lg_603=lg & a<=v_606 & 
a<=v_606 & sm_621=sm_602 & lg_622=pl_604 & sm_621<=lg_622 & 
p_718=v_node2_43_716 & q_719=q_608 & v_606<=qs_605 & 
C(mi_649,sm_621,ma_650,lg_622,a,v_node2_43_716) & v_717=v_606 & 
(q_608=null & qs_605<=lg_603 | q_608!=null & qs_605<=lg_603) & 
(v_node2_43_716=null & mi_649<=ma_650 | v_node2_43_716!=null & 
mi_649<=ma_650) |-  ma_650<=v_717 (may-bug).
                   fc_current_lhs_flow: {FLOW,(1,23)=__flow}}
       FAIL_UNION 
         Trivial fail : MUSTno lemma found in both LHS and RHS nodes (do coercion)
       ;
 Label: [(64::,1 ); (64::,1 ); (63::,1 ); (63::,1 )]
 State:
        
         fe_kind: MUST
         fe_name: logical bug
         fe_locs: {
                   fc_message: 
                    (failure_code=213)  x!=null & x!=null & x!=null & v_node2_51_555'=x & res=v_node2_51_555' |-  res=null (must-bug).
                   fc_current_lhs_flow: {FLOW,(1,5)=__Error}}
       FAIL_UNION 
        
         fe_kind: MAY
         fe_name: logical bug
         fe_locs: {
                   fc_message: 
                    (failure_code=213)  lg_603=lg & qs_605<=lg_603 & v_606<=qs_605 & sm_602=sm & v_606<a & 
v_606<a & sm_656=qs_605 & lg_657=lg_603 & sm_656<=lg_657 & p_776=p_607 & 
q_777=v_node2_48_774 & pl_604<=v_606 & 
C(mi_684,sm_656,ma_685,lg_657,a,v_node2_48_774) & v_775=v_606 & 
(v_node2_48_774=null & mi_684<=ma_685 | v_node2_48_774!=null & 
mi_684<=ma_685) & (p_607=null & sm_602<=pl_604 | p_607!=null & 
sm_602<=pl_604) |-  v_775<=mi_684 (may-bug).
                   fc_current_lhs_flow: {FLOW,(1,23)=__flow}}
       FAIL_UNION 
         Trivial fail : MUSTno lemma found in both LHS and RHS nodes (do coercion)
       
 ]
Successful States:


Context of Verification Failure: File "bst-insert.ss",Line:24,Col:10
Last Proving Location: File "bst-insert.ss",Line:48,Col:3

ERROR: at bst-insert.ss_24_10 
Message: Post condition cannot be derived by the system.
 
Procedure insert$node2~int FAIL-2

Exception Failure("Post condition cannot be derived by the system.") Occurred!

Error(s) detected when checking procedure insert$node2~int

Termination checking result:

Stop Omega... 308 invocations 
0 false contexts at: ()

Total verification time: 3.248201 second(s)
	Time spent in main process: 0.108006 second(s)
	Time spent in child processes: 3.140195 second(s)

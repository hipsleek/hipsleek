
Processing file "bst-del-a.ss"
Parsing bst-del-a.ss ...
Parsing /home2/loris/hg/sl_infer/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure delete$node2~int... 
dprint: bst-del-a.ss:66: ctx:  List of Failesc Context: [FEC(0, 0, 4  [(73::,0 ); (73::,0 ); (68::,0 ); (68::,0 ); (65::,0 ); (65::,0 )];  [(73::,1 ); (73::,1 ); (68::,0 ); (68::,0 ); (65::,0 ); (65::,0 )];  [(69::,0 ); (69::,0 ); (68::,1 ); (68::,1 ); (65::,0 ); (65::,0 )];  [(69::,1 ); (69::,1 ); (68::,1 ); (68::,1 ); (65::,0 ); (65::,0 )])]

Successful States:
[
 Label: [(73::,0 ); (73::,0 ); (68::,0 ); (68::,0 ); (65::,0 ); (65::,0 )]
 State:p_588::bst<sm_583,pl_585>@M[Orig] * q_589::bst<qs_586,lg_584>@M[Orig] * x'::node2<v_587,p_588,q_589>@M[Orig]&pl_585<=v_587 & v_587<=qs_586 & sm_583=sm & lg_584=lg & a'=a & x!=null & v_bool_36_529' & x!=null & v_bool_36_529' & v_587=a' & v_bool_41_525' & v_587=a' & v_bool_41_525' & q_589=null & v_bool_43_523' & q_589=null & v_bool_43_523' & x'=p_588&{FLOW,(20,21)=__norm}
       es_infer_vars/rel: [B]
       es_var_measures: MayLoop;
 Label: [(73::,1 ); (73::,1 ); (68::,0 ); (68::,0 ); (65::,0 ); (65::,0 )]
 State:EXISTS(s1_612,xright_34': p_588::bst<sm_583,pl_585>@M[Orig] * xright_34'::bst<s1_612,b>@M[Orig][LHSCase] * x'::node2<tmp_31',p_588,xright_34'>@M[Orig]&pl_585<=v_587 & v_587<=qs_586 & sm_583=sm & lg_584=lg & x'=x & a'=a & x'!=null & v_bool_36_529' & x'!=null & v_bool_36_529' & v_587=a' & v_bool_41_525' & v_587=a' & v_bool_41_525' & q_589!=null & 175::!(v_bool_43_523') & q_589!=null & !(v_bool_43_523') & s=qs_586 & b=lg_584 & qs_586<=lg_584 & s<=tmp_31' & tmp_31'<=s1_612 & s<=b&{FLOW,(20,21)=__norm})
       es_infer_vars/rel: [B]
       es_var_measures: MayLoop;
 Label: [(69::,0 ); (69::,0 ); (68::,1 ); (68::,1 ); (65::,0 ); (65::,0 )]
 State:EXISTS(s_637,l_638,xright_34': p_588::bst<sm_583,pl_585>@M[Orig] * xright_34'::bst<s_637,l_638>@M[Orig][LHSCase] * x'::node2<v_587,p_588,xright_34'>@M[Orig]&pl_585<=v_587 & v_587<=qs_586 & sm_583=sm & lg_584=lg & x'=x & a'=a & x'!=null & v_bool_36_529' & x'!=null & v_bool_36_529' & v_587!=a' & 163::!(v_bool_41_525') & v_587!=a' & !(v_bool_41_525') & v_587<a' & v_bool_60_524' & v_587<a' & v_bool_60_524' & sm_619=qs_586 & lg_620=lg_584 & qs_586<=lg_584 & sm_619<=s_637 & B(l_638,lg_620) & sm_619<=lg_620&{FLOW,(20,21)=__norm})
       es_infer_vars/rel: [B]
       es_var_measures: MayLoop;
 Label: [(69::,1 ); (69::,1 ); (68::,1 ); (68::,1 ); (65::,0 ); (65::,0 )]
 State:EXISTS(s_657,l_658,xleft_33': q_589::bst<qs_586,lg_584>@M[Orig] * xleft_33'::bst<s_657,l_658>@M[Orig][LHSCase] * x'::node2<v_587,xleft_33',q_589>@M[Orig]&pl_585<=v_587 & v_587<=qs_586 & sm_583=sm & lg_584=lg & x'=x & a'=a & x'!=null & v_bool_36_529' & x'!=null & v_bool_36_529' & v_587!=a' & 163::!(v_bool_41_525') & v_587!=a' & !(v_bool_41_525') & a'<=v_587 & 198::!(v_bool_60_524') & a'<=v_587 & !(v_bool_60_524') & sm_639=sm_583 & lg_640=pl_585 & sm_583<=pl_585 & sm_639<=s_657 & B(l_658,lg_640) & sm_639<=lg_640&{FLOW,(20,21)=__norm})
       es_infer_vars/rel: [B]
       es_var_measures: MayLoop
 ]

( [(69::,1 ); (69::,1 ); (68::,1 ); (68::,1 ); (65::,0 ); (65::,0 )]) :bst-del-a.ss:31: 12: Postcondition cannot be derived from context


(Cause of PostCond Failure):bst-del-a.ss:31: 12:  List of Partial Context: [PC(1, 0) PC(1, 0) PC(1, 0) PC(1, 0) PC(1, 0) PC(1, 0) PC(1, 0) PC(1, 0) PC(1, 0) PC(1, 0) PC(1, 0) PC(1, 0)]
Failed States:
[
 Label: [(69::,1 ); (69::,1 ); (68::,1 ); (68::,1 ); (65::,0 ); (65::,0 )]
 State:
        
         fe_kind: MUST
         fe_name: logical bug
         fe_locs: {
                   fc_message: 
                    (failure_code=213)  x'=x & x'!=null & x'!=null & x'!=null |-  x'=null (must-bug).
                   fc_current_lhs_flow: {FLOW,(1,5)=__Error}}
       FAIL_UNION 
        
         fe_kind: MAY
         fe_name: logical bug
         fe_locs: {
                   fc_message: 
                    (failure_code=213)  sm_583=sm & sm_639=sm_583 & sm_583<=pl_585 & pl_585<=v_587 & lg_584=lg & 
v_587!=a & v_587!=a & a<=v_587 & a<=v_587 & lg_640=pl_585 & sm_639<=s_946 & 
sm_639<=lg_640 & p_950=xleft_948 & q_951=q_589 & v_587<=qs_586 & 
B(l_947,lg_640) & v_949=v_587 & (q_589=null & qs_586<=lg_584 | q_589!=null & 
qs_586<=lg_584) & (xleft_948=null & s_946<=l_947 | xleft_948!=null & 
s_946<=l_947) |-  l_947<=v_949 (may-bug).
                   fc_current_lhs_flow: {FLOW,(1,23)=__flow}}
       FAIL_UNION 
         Trivial fail : MUSTno lemma found in both LHS and RHS nodes (do coercion)
       
 ]
Successful States:
,
Failed States:
[
 Label: [(69::,1 ); (69::,1 ); (68::,1 ); (68::,1 ); (65::,0 ); (65::,0 )]
 State:
        
         fe_kind: MUST
         fe_name: logical bug
         fe_locs: {
                   fc_message: 
                    (failure_code=213)  x'=x & x'!=null & x'!=null & x'!=null |-  x'=null (must-bug).
                   fc_current_lhs_flow: {FLOW,(1,5)=__Error}}
       FAIL_UNION 
        
         fe_kind: MAY
         fe_name: logical bug
         fe_locs: {
                   fc_message: 
                    (failure_code=213)  sm_583=sm & sm_639=sm_583 & sm_583<=pl_585 & pl_585<=v_587 & lg_584=lg & 
v_587!=a & v_587!=a & a<=v_587 & a<=v_587 & lg_640=pl_585 & sm_639<=s_946 & 
sm_639<=lg_640 & p_950=xleft_948 & q_951=q_589 & v_587<=qs_586 & 
B(l_947,lg_640) & v_949=v_587 & (q_589=null & qs_586<=lg_584 | q_589!=null & 
qs_586<=lg_584) & (xleft_948=null & s_946<=l_947 | xleft_948!=null & 
s_946<=l_947) |-  l_947<=v_949 (may-bug).
                   fc_current_lhs_flow: {FLOW,(1,23)=__flow}}
       FAIL_UNION 
         Trivial fail : MUSTno lemma found in both LHS and RHS nodes (do coercion)
       
 ]
Successful States:
,
Failed States:
[
 Label: [(69::,1 ); (69::,1 ); (68::,1 ); (68::,1 ); (65::,0 ); (65::,0 )]
 State:
        
         fe_kind: MUST
         fe_name: logical bug
         fe_locs: {
                   fc_message: 
                    (failure_code=213)  x'=x & x'!=null & x'!=null & x'!=null |-  x'=null (must-bug).
                   fc_current_lhs_flow: {FLOW,(1,5)=__Error}}
       FAIL_UNION 
        
         fe_kind: MAY
         fe_name: logical bug
         fe_locs: {
                   fc_message: 
                    (failure_code=213)  sm_583=sm & sm_639=sm_583 & sm_583<=pl_585 & pl_585<=v_587 & lg_584=lg & 
v_587!=a & v_587!=a & a<=v_587 & a<=v_587 & lg_640=pl_585 & sm_639<=s_946 & 
sm_639<=lg_640 & p_950=xleft_948 & q_951=q_589 & v_587<=qs_586 & 
B(l_947,lg_640) & v_949=v_587 & (q_589=null & qs_586<=lg_584 | q_589!=null & 
qs_586<=lg_584) & (xleft_948=null & s_946<=l_947 | xleft_948!=null & 
s_946<=l_947) |-  l_947<=v_949 (may-bug).
                   fc_current_lhs_flow: {FLOW,(1,23)=__flow}}
       FAIL_UNION 
         Trivial fail : MUSTno lemma found in both LHS and RHS nodes (do coercion)
       
 ]
Successful States:
,
Failed States:
[
 Label: [(69::,1 ); (69::,1 ); (68::,1 ); (68::,1 ); (65::,0 ); (65::,0 )]
 State:
        
         fe_kind: MUST
         fe_name: logical bug
         fe_locs: {
                   fc_message: 
                    (failure_code=213)  x'=x & x'!=null & x'!=null & x'!=null |-  x'=null (must-bug).
                   fc_current_lhs_flow: {FLOW,(1,5)=__Error}}
       FAIL_UNION 
        
         fe_kind: MAY
         fe_name: logical bug
         fe_locs: {
                   fc_message: 
                    (failure_code=213)  sm_583=sm & sm_639=sm_583 & sm_583<=pl_585 & pl_585<=v_587 & lg_584=lg & 
v_587!=a & v_587!=a & a<=v_587 & a<=v_587 & lg_640=pl_585 & sm_639<=s_946 & 
sm_639<=lg_640 & p_950=xleft_948 & q_951=q_589 & v_587<=qs_586 & 
B(l_947,lg_640) & v_949=v_587 & (q_589=null & qs_586<=lg_584 | q_589!=null & 
qs_586<=lg_584) & (xleft_948=null & s_946<=l_947 | xleft_948!=null & 
s_946<=l_947) |-  l_947<=v_949 (may-bug).
                   fc_current_lhs_flow: {FLOW,(1,23)=__flow}}
       FAIL_UNION 
         Trivial fail : MUSTno lemma found in both LHS and RHS nodes (do coercion)
       
 ]
Successful States:
,
Failed States:
[
 Label: [(69::,1 ); (69::,1 ); (68::,1 ); (68::,1 ); (65::,0 ); (65::,0 )]
 State:
        
         fe_kind: MUST
         fe_name: logical bug
         fe_locs: {
                   fc_message: 
                    (failure_code=213)  x'=x & x'!=null & x'!=null & x'!=null |-  x'=null (must-bug).
                   fc_current_lhs_flow: {FLOW,(1,5)=__Error}}
       FAIL_UNION 
        
         fe_kind: MAY
         fe_name: logical bug
         fe_locs: {
                   fc_message: 
                    (failure_code=213)  sm_583=sm & sm_639=sm_583 & sm_583<=pl_585 & pl_585<=v_587 & lg_584=lg & 
v_587!=a & v_587!=a & a<=v_587 & a<=v_587 & lg_640=pl_585 & sm_639<=s_946 & 
sm_639<=lg_640 & p_950=xleft_948 & q_951=q_589 & v_587<=qs_586 & 
B(l_947,lg_640) & v_949=v_587 & (q_589=null & qs_586<=lg_584 | q_589!=null & 
qs_586<=lg_584) & (xleft_948=null & s_946<=l_947 | xleft_948!=null & 
s_946<=l_947) |-  l_947<=v_949 (may-bug).
                   fc_current_lhs_flow: {FLOW,(1,23)=__flow}}
       FAIL_UNION 
         Trivial fail : MUSTno lemma found in both LHS and RHS nodes (do coercion)
       
 ]
Successful States:
,
Failed States:
[
 Label: [(69::,1 ); (69::,1 ); (68::,1 ); (68::,1 ); (65::,0 ); (65::,0 )]
 State:
        
         fe_kind: MUST
         fe_name: logical bug
         fe_locs: {
                   fc_message: 
                    (failure_code=213)  x'=x & x'!=null & x'!=null & x'!=null |-  x'=null (must-bug).
                   fc_current_lhs_flow: {FLOW,(1,5)=__Error}}
       FAIL_UNION 
        
         fe_kind: MAY
         fe_name: logical bug
         fe_locs: {
                   fc_message: 
                    (failure_code=213)  sm_583=sm & sm_639=sm_583 & sm_583<=pl_585 & pl_585<=v_587 & lg_584=lg & 
v_587!=a & v_587!=a & a<=v_587 & a<=v_587 & lg_640=pl_585 & sm_639<=s_946 & 
sm_639<=lg_640 & p_950=xleft_948 & q_951=q_589 & v_587<=qs_586 & 
B(l_947,lg_640) & v_949=v_587 & (q_589=null & qs_586<=lg_584 | q_589!=null & 
qs_586<=lg_584) & (xleft_948=null & s_946<=l_947 | xleft_948!=null & 
s_946<=l_947) |-  l_947<=v_949 (may-bug).
                   fc_current_lhs_flow: {FLOW,(1,23)=__flow}}
       FAIL_UNION 
         Trivial fail : MUSTno lemma found in both LHS and RHS nodes (do coercion)
       
 ]
Successful States:
,
Failed States:
[
 Label: [(69::,1 ); (69::,1 ); (68::,1 ); (68::,1 ); (65::,0 ); (65::,0 )]
 State:
        
         fe_kind: MUST
         fe_name: logical bug
         fe_locs: {
                   fc_message: 
                    (failure_code=213)  x'=x & x'!=null & x'!=null & x'!=null |-  x'=null (must-bug).
                   fc_current_lhs_flow: {FLOW,(1,5)=__Error}}
       FAIL_UNION 
        
         fe_kind: MAY
         fe_name: logical bug
         fe_locs: {
                   fc_message: 
                    (failure_code=213)  sm_583=sm & sm_639=sm_583 & sm_583<=pl_585 & pl_585<=v_587 & lg_584=lg & 
v_587!=a & v_587!=a & a<=v_587 & a<=v_587 & lg_640=pl_585 & sm_639<=s_946 & 
sm_639<=lg_640 & p_950=xleft_948 & q_951=q_589 & v_587<=qs_586 & 
B(l_947,lg_640) & v_949=v_587 & (q_589=null & qs_586<=lg_584 | q_589!=null & 
qs_586<=lg_584) & (xleft_948=null & s_946<=l_947 | xleft_948!=null & 
s_946<=l_947) |-  l_947<=v_949 (may-bug).
                   fc_current_lhs_flow: {FLOW,(1,23)=__flow}}
       FAIL_UNION 
         Trivial fail : MUSTno lemma found in both LHS and RHS nodes (do coercion)
       
 ]
Successful States:
,
Failed States:
[
 Label: [(69::,1 ); (69::,1 ); (68::,1 ); (68::,1 ); (65::,0 ); (65::,0 )]
 State:
        
         fe_kind: MUST
         fe_name: logical bug
         fe_locs: {
                   fc_message: 
                    (failure_code=213)  x'=x & x'!=null & x'!=null & x'!=null |-  x'=null (must-bug).
                   fc_current_lhs_flow: {FLOW,(1,5)=__Error}}
       FAIL_UNION 
        
         fe_kind: MAY
         fe_name: logical bug
         fe_locs: {
                   fc_message: 
                    (failure_code=213)  sm_583=sm & sm_639=sm_583 & sm_583<=pl_585 & pl_585<=v_587 & lg_584=lg & 
v_587!=a & v_587!=a & a<=v_587 & a<=v_587 & lg_640=pl_585 & sm_639<=s_946 & 
sm_639<=lg_640 & p_950=xleft_948 & q_951=q_589 & v_587<=qs_586 & 
B(l_947,lg_640) & v_949=v_587 & (q_589=null & qs_586<=lg_584 | q_589!=null & 
qs_586<=lg_584) & (xleft_948=null & s_946<=l_947 | xleft_948!=null & 
s_946<=l_947) |-  l_947<=v_949 (may-bug).
                   fc_current_lhs_flow: {FLOW,(1,23)=__flow}}
       FAIL_UNION 
         Trivial fail : MUSTno lemma found in both LHS and RHS nodes (do coercion)
       
 ]
Successful States:
,
Failed States:
[
 Label: [(69::,1 ); (69::,1 ); (68::,1 ); (68::,1 ); (65::,0 ); (65::,0 )]
 State:
        
         fe_kind: MUST
         fe_name: logical bug
         fe_locs: {
                   fc_message: 
                    (failure_code=213)  x'=x & x'!=null & x'!=null & x'!=null |-  x'=null (must-bug).
                   fc_current_lhs_flow: {FLOW,(1,5)=__Error}}
       FAIL_UNION 
        
         fe_kind: MAY
         fe_name: logical bug
         fe_locs: {
                   fc_message: 
                    (failure_code=213)  sm_583=sm & sm_639=sm_583 & sm_583<=pl_585 & pl_585<=v_587 & lg_584=lg & 
v_587!=a & v_587!=a & a<=v_587 & a<=v_587 & lg_640=pl_585 & sm_639<=s_946 & 
sm_639<=lg_640 & p_950=xleft_948 & q_951=q_589 & v_587<=qs_586 & 
B(l_947,lg_640) & v_949=v_587 & (q_589=null & qs_586<=lg_584 | q_589!=null & 
qs_586<=lg_584) & (xleft_948=null & s_946<=l_947 | xleft_948!=null & 
s_946<=l_947) |-  l_947<=v_949 (may-bug).
                   fc_current_lhs_flow: {FLOW,(1,23)=__flow}}
       FAIL_UNION 
         Trivial fail : MUSTno lemma found in both LHS and RHS nodes (do coercion)
       
 ]
Successful States:
,
Failed States:
[
 Label: [(69::,1 ); (69::,1 ); (68::,1 ); (68::,1 ); (65::,0 ); (65::,0 )]
 State:
        
         fe_kind: MUST
         fe_name: logical bug
         fe_locs: {
                   fc_message: 
                    (failure_code=213)  x'=x & x'!=null & x'!=null & x'!=null |-  x'=null (must-bug).
                   fc_current_lhs_flow: {FLOW,(1,5)=__Error}}
       FAIL_UNION 
        
         fe_kind: MAY
         fe_name: logical bug
         fe_locs: {
                   fc_message: 
                    (failure_code=213)  sm_583=sm & sm_639=sm_583 & sm_583<=pl_585 & pl_585<=v_587 & lg_584=lg & 
v_587!=a & v_587!=a & a<=v_587 & a<=v_587 & lg_640=pl_585 & sm_639<=s_946 & 
sm_639<=lg_640 & p_950=xleft_948 & q_951=q_589 & v_587<=qs_586 & 
B(l_947,lg_640) & v_949=v_587 & (q_589=null & qs_586<=lg_584 | q_589!=null & 
qs_586<=lg_584) & (xleft_948=null & s_946<=l_947 | xleft_948!=null & 
s_946<=l_947) |-  l_947<=v_949 (may-bug).
                   fc_current_lhs_flow: {FLOW,(1,23)=__flow}}
       FAIL_UNION 
         Trivial fail : MUSTno lemma found in both LHS and RHS nodes (do coercion)
       
 ]
Successful States:
,
Failed States:
[
 Label: [(69::,1 ); (69::,1 ); (68::,1 ); (68::,1 ); (65::,0 ); (65::,0 )]
 State:
        
         fe_kind: MUST
         fe_name: logical bug
         fe_locs: {
                   fc_message: 
                    (failure_code=213)  x'=x & x'!=null & x'!=null & x'!=null |-  x'=null (must-bug).
                   fc_current_lhs_flow: {FLOW,(1,5)=__Error}}
       FAIL_UNION 
        
         fe_kind: MAY
         fe_name: logical bug
         fe_locs: {
                   fc_message: 
                    (failure_code=213)  sm_583=sm & sm_639=sm_583 & sm_583<=pl_585 & pl_585<=v_587 & lg_584=lg & 
v_587!=a & v_587!=a & a<=v_587 & a<=v_587 & lg_640=pl_585 & sm_639<=s_946 & 
sm_639<=lg_640 & p_950=xleft_948 & q_951=q_589 & v_587<=qs_586 & 
B(l_947,lg_640) & v_949=v_587 & (q_589=null & qs_586<=lg_584 | q_589!=null & 
qs_586<=lg_584) & (xleft_948=null & s_946<=l_947 | xleft_948!=null & 
s_946<=l_947) |-  l_947<=v_949 (may-bug).
                   fc_current_lhs_flow: {FLOW,(1,23)=__flow}}
       FAIL_UNION 
         Trivial fail : MUSTno lemma found in both LHS and RHS nodes (do coercion)
       
 ]
Successful States:
,
Failed States:
[
 Label: [(69::,1 ); (69::,1 ); (68::,1 ); (68::,1 ); (65::,0 ); (65::,0 )]
 State:
        
         fe_kind: MUST
         fe_name: logical bug
         fe_locs: {
                   fc_message: 
                    (failure_code=213)  x'=x & x'!=null & x'!=null & x'!=null |-  x'=null (must-bug).
                   fc_current_lhs_flow: {FLOW,(1,5)=__Error}}
       FAIL_UNION 
        
         fe_kind: MAY
         fe_name: logical bug
         fe_locs: {
                   fc_message: 
                    (failure_code=213)  sm_583=sm & sm_639=sm_583 & sm_583<=pl_585 & pl_585<=v_587 & lg_584=lg & 
v_587!=a & v_587!=a & a<=v_587 & a<=v_587 & lg_640=pl_585 & sm_639<=s_946 & 
sm_639<=lg_640 & p_950=xleft_948 & q_951=q_589 & v_587<=qs_586 & 
B(l_947,lg_640) & v_949=v_587 & (q_589=null & qs_586<=lg_584 | q_589!=null & 
qs_586<=lg_584) & (xleft_948=null & s_946<=l_947 | xleft_948!=null & 
s_946<=l_947) |-  l_947<=v_949 (may-bug).
                   fc_current_lhs_flow: {FLOW,(1,23)=__flow}}
       FAIL_UNION 
         Trivial fail : MUSTno lemma found in both LHS and RHS nodes (do coercion)
       
 ]
Successful States:


Context of Verification Failure: File "bst-del-a.ss",Line:31,Col:12
Last Proving Location: File "bst-del-a.ss",Line:69,Col:6

ERROR: at bst-del-a.ss_31_12 
Message: Post condition cannot be derived by the system.
 
Procedure delete$node2~int FAIL-2

Exception Failure("Post condition cannot be derived by the system.") Occurred!

Error(s) detected when checking procedure delete$node2~int

Termination checking result:

Stop Omega... 521 invocations 
0 false contexts at: ()

Total verification time: 4.028249 second(s)
	Time spent in main process: 0.228013 second(s)
	Time spent in child processes: 3.800236 second(s)

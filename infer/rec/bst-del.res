
Processing file "bst-del.ss"
Parsing bst-del.ss ...
Parsing /home2/loris/hg/sl_infer/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure delete$node2~int... 
dprint: bst-del.ss:67: ctx:  List of Failesc Context: [FEC(0, 0, 4  [(73::,0 ); (73::,0 ); (68::,0 ); (68::,0 ); (65::,0 ); (65::,0 )];  [(73::,1 ); (73::,1 ); (68::,0 ); (68::,0 ); (65::,0 ); (65::,0 )];  [(69::,0 ); (69::,0 ); (68::,1 ); (68::,1 ); (65::,0 ); (65::,0 )];  [(69::,1 ); (69::,1 ); (68::,1 ); (68::,1 ); (65::,0 ); (65::,0 )])]

Successful States:
[
 Label: [(73::,0 ); (73::,0 ); (68::,0 ); (68::,0 ); (65::,0 ); (65::,0 )]
 State:p_589::bst<sm_584,pl_586>@M[Orig] * q_590::bst<qs_587,lg_585>@M[Orig] * x'::node2<v_588,p_589,q_590>@M[Orig]&pl_586<=v_588 & v_588<=qs_587 & sm_584=sm & lg_585=lg & a'=a & x!=null & v_bool_37_530' & x!=null & v_bool_37_530' & v_588=a' & v_bool_42_526' & v_588=a' & v_bool_42_526' & q_590=null & v_bool_44_524' & q_590=null & v_bool_44_524' & x'=p_589&{FLOW,(20,21)=__norm}
       es_infer_vars/rel: [B]
       es_var_measures: MayLoop;
 Label: [(73::,1 ); (73::,1 ); (68::,0 ); (68::,0 ); (65::,0 ); (65::,0 )]
 State:EXISTS(s1_613,xright_34': p_589::bst<sm_584,pl_586>@M[Orig] * xright_34'::bst<s1_613,b>@M[Orig][LHSCase] * x'::node2<tmp_31',p_589,xright_34'>@M[Orig]&pl_586<=v_588 & v_588<=qs_587 & sm_584=sm & lg_585=lg & x'=x & a'=a & x'!=null & v_bool_37_530' & x'!=null & v_bool_37_530' & v_588=a' & v_bool_42_526' & v_588=a' & v_bool_42_526' & q_590!=null & 175::!(v_bool_44_524') & q_590!=null & !(v_bool_44_524') & s=qs_587 & b=lg_585 & qs_587<=lg_585 & s<=tmp_31' & tmp_31'<=s1_613 & s<=b&{FLOW,(20,21)=__norm})
       es_infer_vars/rel: [B]
       es_var_measures: MayLoop;
 Label: [(69::,0 ); (69::,0 ); (68::,1 ); (68::,1 ); (65::,0 ); (65::,0 )]
 State:EXISTS(s_638,l_639,xright_34': p_589::bst<sm_584,pl_586>@M[Orig] * xright_34'::bst<s_638,l_639>@M[Orig][LHSCase] * x'::node2<v_588,p_589,xright_34'>@M[Orig]&pl_586<=v_588 & v_588<=qs_587 & sm_584=sm & lg_585=lg & x'=x & a'=a & x'!=null & v_bool_37_530' & x'!=null & v_bool_37_530' & v_588!=a' & 163::!(v_bool_42_526') & v_588!=a' & !(v_bool_42_526') & v_588<a' & v_bool_61_525' & v_588<a' & v_bool_61_525' & sm_620=qs_587 & lg_621=lg_585 & qs_587<=lg_585 & B(sm_620,s_638,l_639,lg_621) & sm_620<=lg_621&{FLOW,(20,21)=__norm})
       es_infer_vars/rel: [B]
       es_var_measures: MayLoop;
 Label: [(69::,1 ); (69::,1 ); (68::,1 ); (68::,1 ); (65::,0 ); (65::,0 )]
 State:EXISTS(s_658,l_659,xleft_33': q_590::bst<qs_587,lg_585>@M[Orig] * xleft_33'::bst<s_658,l_659>@M[Orig][LHSCase] * x'::node2<v_588,xleft_33',q_590>@M[Orig]&pl_586<=v_588 & v_588<=qs_587 & sm_584=sm & lg_585=lg & x'=x & a'=a & x'!=null & v_bool_37_530' & x'!=null & v_bool_37_530' & v_588!=a' & 163::!(v_bool_42_526') & v_588!=a' & !(v_bool_42_526') & a'<=v_588 & 198::!(v_bool_61_525') & a'<=v_588 & !(v_bool_61_525') & sm_640=sm_584 & lg_641=pl_586 & sm_584<=pl_586 & B(sm_640,s_658,l_659,lg_641) & sm_640<=lg_641&{FLOW,(20,21)=__norm})
       es_infer_vars/rel: [B]
       es_var_measures: MayLoop
 ]

( [(69::,0 ); (69::,0 ); (68::,1 ); (68::,1 ); (65::,0 ); (65::,0 )]) :bst-del.ss:32: 12: Postcondition cannot be derived from context


(Cause of PostCond Failure):bst-del.ss:32: 12:  List of Partial Context: [PC(2, 0) PC(2, 0) PC(2, 0) PC(2, 0) PC(2, 0) PC(2, 0) PC(2, 0) PC(2, 0) PC(2, 0) PC(2, 0) PC(2, 0) PC(2, 0)]
Failed States:
[
 Label: [(69::,0 ); (69::,0 ); (68::,1 ); (68::,1 ); (65::,0 ); (65::,0 )]
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
                    (failure_code=213)  lg_585=lg & qs_587<=lg_585 & v_588<=qs_587 & sm_584=sm & v_588!=a & 
v_588!=a & v_588<a & v_588<a & sm_620=qs_587 & lg_621=lg_585 & 
sm_620<=lg_621 & p_896=p_589 & q_897=xright_894 & pl_586<=v_588 & 
B(sm_620,s_892,l_893,lg_621) & v_895=v_588 & (xright_894=null & 
s_892<=l_893 | xright_894!=null & s_892<=l_893) & (p_589=null & 
sm_584<=pl_586 | p_589!=null & sm_584<=pl_586) |-  v_895<=s_892 (may-bug).
                   fc_current_lhs_flow: {FLOW,(1,23)=__flow}}
       FAIL_UNION 
         Trivial fail : MUSTno lemma found in both LHS and RHS nodes (do coercion)
       ;
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
                    (failure_code=213)  sm_584=sm & sm_584<=pl_586 & pl_586<=v_588 & lg_585=lg & v_588!=a & 
v_588!=a & a<=v_588 & a<=v_588 & sm_640=sm_584 & lg_641=pl_586 & 
sm_640<=lg_641 & p_950=xleft_948 & q_951=q_590 & v_588<=qs_587 & 
B(sm_640,s_946,l_947,lg_641) & v_949=v_588 & (q_590=null & qs_587<=lg_585 | 
q_590!=null & qs_587<=lg_585) & (xleft_948=null & s_946<=l_947 | 
xleft_948!=null & s_946<=l_947) |-  l_947<=v_949 (may-bug).
                   fc_current_lhs_flow: {FLOW,(1,23)=__flow}}
       FAIL_UNION 
         Trivial fail : MUSTno lemma found in both LHS and RHS nodes (do coercion)
       
 ]
Successful States:
,
Failed States:
[
 Label: [(69::,0 ); (69::,0 ); (68::,1 ); (68::,1 ); (65::,0 ); (65::,0 )]
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
                    (failure_code=213)  lg_585=lg & qs_587<=lg_585 & v_588<=qs_587 & sm_584=sm & v_588!=a & 
v_588!=a & v_588<a & v_588<a & sm_620=qs_587 & lg_621=lg_585 & 
sm_620<=lg_621 & p_896=p_589 & q_897=xright_894 & pl_586<=v_588 & 
B(sm_620,s_892,l_893,lg_621) & v_895=v_588 & (xright_894=null & 
s_892<=l_893 | xright_894!=null & s_892<=l_893) & (p_589=null & 
sm_584<=pl_586 | p_589!=null & sm_584<=pl_586) |-  v_895<=s_892 (may-bug).
                   fc_current_lhs_flow: {FLOW,(1,23)=__flow}}
       FAIL_UNION 
         Trivial fail : MUSTno lemma found in both LHS and RHS nodes (do coercion)
       ;
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
                    (failure_code=213)  sm_584=sm & sm_584<=pl_586 & pl_586<=v_588 & lg_585=lg & v_588!=a & 
v_588!=a & a<=v_588 & a<=v_588 & sm_640=sm_584 & lg_641=pl_586 & 
sm_640<=lg_641 & p_950=xleft_948 & q_951=q_590 & v_588<=qs_587 & 
B(sm_640,s_946,l_947,lg_641) & v_949=v_588 & (q_590=null & qs_587<=lg_585 | 
q_590!=null & qs_587<=lg_585) & (xleft_948=null & s_946<=l_947 | 
xleft_948!=null & s_946<=l_947) |-  l_947<=v_949 (may-bug).
                   fc_current_lhs_flow: {FLOW,(1,23)=__flow}}
       FAIL_UNION 
         Trivial fail : MUSTno lemma found in both LHS and RHS nodes (do coercion)
       
 ]
Successful States:
,
Failed States:
[
 Label: [(69::,0 ); (69::,0 ); (68::,1 ); (68::,1 ); (65::,0 ); (65::,0 )]
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
                    (failure_code=213)  lg_585=lg & qs_587<=lg_585 & v_588<=qs_587 & sm_584=sm & v_588!=a & 
v_588!=a & v_588<a & v_588<a & sm_620=qs_587 & lg_621=lg_585 & 
sm_620<=lg_621 & p_896=p_589 & q_897=xright_894 & pl_586<=v_588 & 
B(sm_620,s_892,l_893,lg_621) & v_895=v_588 & (xright_894=null & 
s_892<=l_893 | xright_894!=null & s_892<=l_893) & (p_589=null & 
sm_584<=pl_586 | p_589!=null & sm_584<=pl_586) |-  v_895<=s_892 (may-bug).
                   fc_current_lhs_flow: {FLOW,(1,23)=__flow}}
       FAIL_UNION 
         Trivial fail : MUSTno lemma found in both LHS and RHS nodes (do coercion)
       ;
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
                    (failure_code=213)  sm_584=sm & sm_584<=pl_586 & pl_586<=v_588 & lg_585=lg & v_588!=a & 
v_588!=a & a<=v_588 & a<=v_588 & sm_640=sm_584 & lg_641=pl_586 & 
sm_640<=lg_641 & p_950=xleft_948 & q_951=q_590 & v_588<=qs_587 & 
B(sm_640,s_946,l_947,lg_641) & v_949=v_588 & (q_590=null & qs_587<=lg_585 | 
q_590!=null & qs_587<=lg_585) & (xleft_948=null & s_946<=l_947 | 
xleft_948!=null & s_946<=l_947) |-  l_947<=v_949 (may-bug).
                   fc_current_lhs_flow: {FLOW,(1,23)=__flow}}
       FAIL_UNION 
         Trivial fail : MUSTno lemma found in both LHS and RHS nodes (do coercion)
       
 ]
Successful States:
,
Failed States:
[
 Label: [(69::,0 ); (69::,0 ); (68::,1 ); (68::,1 ); (65::,0 ); (65::,0 )]
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
                    (failure_code=213)  lg_585=lg & qs_587<=lg_585 & v_588<=qs_587 & sm_584=sm & v_588!=a & 
v_588!=a & v_588<a & v_588<a & sm_620=qs_587 & lg_621=lg_585 & 
sm_620<=lg_621 & p_896=p_589 & q_897=xright_894 & pl_586<=v_588 & 
B(sm_620,s_892,l_893,lg_621) & v_895=v_588 & (xright_894=null & 
s_892<=l_893 | xright_894!=null & s_892<=l_893) & (p_589=null & 
sm_584<=pl_586 | p_589!=null & sm_584<=pl_586) |-  v_895<=s_892 (may-bug).
                   fc_current_lhs_flow: {FLOW,(1,23)=__flow}}
       FAIL_UNION 
         Trivial fail : MUSTno lemma found in both LHS and RHS nodes (do coercion)
       ;
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
                    (failure_code=213)  sm_584=sm & sm_584<=pl_586 & pl_586<=v_588 & lg_585=lg & v_588!=a & 
v_588!=a & a<=v_588 & a<=v_588 & sm_640=sm_584 & lg_641=pl_586 & 
sm_640<=lg_641 & p_950=xleft_948 & q_951=q_590 & v_588<=qs_587 & 
B(sm_640,s_946,l_947,lg_641) & v_949=v_588 & (q_590=null & qs_587<=lg_585 | 
q_590!=null & qs_587<=lg_585) & (xleft_948=null & s_946<=l_947 | 
xleft_948!=null & s_946<=l_947) |-  l_947<=v_949 (may-bug).
                   fc_current_lhs_flow: {FLOW,(1,23)=__flow}}
       FAIL_UNION 
         Trivial fail : MUSTno lemma found in both LHS and RHS nodes (do coercion)
       
 ]
Successful States:
,
Failed States:
[
 Label: [(69::,0 ); (69::,0 ); (68::,1 ); (68::,1 ); (65::,0 ); (65::,0 )]
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
                    (failure_code=213)  lg_585=lg & qs_587<=lg_585 & v_588<=qs_587 & sm_584=sm & v_588!=a & 
v_588!=a & v_588<a & v_588<a & sm_620=qs_587 & lg_621=lg_585 & 
sm_620<=lg_621 & p_896=p_589 & q_897=xright_894 & pl_586<=v_588 & 
B(sm_620,s_892,l_893,lg_621) & v_895=v_588 & (xright_894=null & 
s_892<=l_893 | xright_894!=null & s_892<=l_893) & (p_589=null & 
sm_584<=pl_586 | p_589!=null & sm_584<=pl_586) |-  v_895<=s_892 (may-bug).
                   fc_current_lhs_flow: {FLOW,(1,23)=__flow}}
       FAIL_UNION 
         Trivial fail : MUSTno lemma found in both LHS and RHS nodes (do coercion)
       ;
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
                    (failure_code=213)  sm_584=sm & sm_584<=pl_586 & pl_586<=v_588 & lg_585=lg & v_588!=a & 
v_588!=a & a<=v_588 & a<=v_588 & sm_640=sm_584 & lg_641=pl_586 & 
sm_640<=lg_641 & p_950=xleft_948 & q_951=q_590 & v_588<=qs_587 & 
B(sm_640,s_946,l_947,lg_641) & v_949=v_588 & (q_590=null & qs_587<=lg_585 | 
q_590!=null & qs_587<=lg_585) & (xleft_948=null & s_946<=l_947 | 
xleft_948!=null & s_946<=l_947) |-  l_947<=v_949 (may-bug).
                   fc_current_lhs_flow: {FLOW,(1,23)=__flow}}
       FAIL_UNION 
         Trivial fail : MUSTno lemma found in both LHS and RHS nodes (do coercion)
       
 ]
Successful States:
,
Failed States:
[
 Label: [(69::,0 ); (69::,0 ); (68::,1 ); (68::,1 ); (65::,0 ); (65::,0 )]
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
                    (failure_code=213)  lg_585=lg & qs_587<=lg_585 & v_588<=qs_587 & sm_584=sm & v_588!=a & 
v_588!=a & v_588<a & v_588<a & sm_620=qs_587 & lg_621=lg_585 & 
sm_620<=lg_621 & p_896=p_589 & q_897=xright_894 & pl_586<=v_588 & 
B(sm_620,s_892,l_893,lg_621) & v_895=v_588 & (xright_894=null & 
s_892<=l_893 | xright_894!=null & s_892<=l_893) & (p_589=null & 
sm_584<=pl_586 | p_589!=null & sm_584<=pl_586) |-  v_895<=s_892 (may-bug).
                   fc_current_lhs_flow: {FLOW,(1,23)=__flow}}
       FAIL_UNION 
         Trivial fail : MUSTno lemma found in both LHS and RHS nodes (do coercion)
       ;
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
                    (failure_code=213)  sm_584=sm & sm_584<=pl_586 & pl_586<=v_588 & lg_585=lg & v_588!=a & 
v_588!=a & a<=v_588 & a<=v_588 & sm_640=sm_584 & lg_641=pl_586 & 
sm_640<=lg_641 & p_950=xleft_948 & q_951=q_590 & v_588<=qs_587 & 
B(sm_640,s_946,l_947,lg_641) & v_949=v_588 & (q_590=null & qs_587<=lg_585 | 
q_590!=null & qs_587<=lg_585) & (xleft_948=null & s_946<=l_947 | 
xleft_948!=null & s_946<=l_947) |-  l_947<=v_949 (may-bug).
                   fc_current_lhs_flow: {FLOW,(1,23)=__flow}}
       FAIL_UNION 
         Trivial fail : MUSTno lemma found in both LHS and RHS nodes (do coercion)
       
 ]
Successful States:
,
Failed States:
[
 Label: [(69::,0 ); (69::,0 ); (68::,1 ); (68::,1 ); (65::,0 ); (65::,0 )]
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
                    (failure_code=213)  lg_585=lg & qs_587<=lg_585 & v_588<=qs_587 & sm_584=sm & v_588!=a & 
v_588!=a & v_588<a & v_588<a & sm_620=qs_587 & lg_621=lg_585 & 
sm_620<=lg_621 & p_896=p_589 & q_897=xright_894 & pl_586<=v_588 & 
B(sm_620,s_892,l_893,lg_621) & v_895=v_588 & (xright_894=null & 
s_892<=l_893 | xright_894!=null & s_892<=l_893) & (p_589=null & 
sm_584<=pl_586 | p_589!=null & sm_584<=pl_586) |-  v_895<=s_892 (may-bug).
                   fc_current_lhs_flow: {FLOW,(1,23)=__flow}}
       FAIL_UNION 
         Trivial fail : MUSTno lemma found in both LHS and RHS nodes (do coercion)
       ;
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
                    (failure_code=213)  sm_584=sm & sm_584<=pl_586 & pl_586<=v_588 & lg_585=lg & v_588!=a & 
v_588!=a & a<=v_588 & a<=v_588 & sm_640=sm_584 & lg_641=pl_586 & 
sm_640<=lg_641 & p_950=xleft_948 & q_951=q_590 & v_588<=qs_587 & 
B(sm_640,s_946,l_947,lg_641) & v_949=v_588 & (q_590=null & qs_587<=lg_585 | 
q_590!=null & qs_587<=lg_585) & (xleft_948=null & s_946<=l_947 | 
xleft_948!=null & s_946<=l_947) |-  l_947<=v_949 (may-bug).
                   fc_current_lhs_flow: {FLOW,(1,23)=__flow}}
       FAIL_UNION 
         Trivial fail : MUSTno lemma found in both LHS and RHS nodes (do coercion)
       
 ]
Successful States:
,
Failed States:
[
 Label: [(69::,0 ); (69::,0 ); (68::,1 ); (68::,1 ); (65::,0 ); (65::,0 )]
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
                    (failure_code=213)  lg_585=lg & qs_587<=lg_585 & v_588<=qs_587 & sm_584=sm & v_588!=a & 
v_588!=a & v_588<a & v_588<a & sm_620=qs_587 & lg_621=lg_585 & 
sm_620<=lg_621 & p_896=p_589 & q_897=xright_894 & pl_586<=v_588 & 
B(sm_620,s_892,l_893,lg_621) & v_895=v_588 & (xright_894=null & 
s_892<=l_893 | xright_894!=null & s_892<=l_893) & (p_589=null & 
sm_584<=pl_586 | p_589!=null & sm_584<=pl_586) |-  v_895<=s_892 (may-bug).
                   fc_current_lhs_flow: {FLOW,(1,23)=__flow}}
       FAIL_UNION 
         Trivial fail : MUSTno lemma found in both LHS and RHS nodes (do coercion)
       ;
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
                    (failure_code=213)  sm_584=sm & sm_584<=pl_586 & pl_586<=v_588 & lg_585=lg & v_588!=a & 
v_588!=a & a<=v_588 & a<=v_588 & sm_640=sm_584 & lg_641=pl_586 & 
sm_640<=lg_641 & p_950=xleft_948 & q_951=q_590 & v_588<=qs_587 & 
B(sm_640,s_946,l_947,lg_641) & v_949=v_588 & (q_590=null & qs_587<=lg_585 | 
q_590!=null & qs_587<=lg_585) & (xleft_948=null & s_946<=l_947 | 
xleft_948!=null & s_946<=l_947) |-  l_947<=v_949 (may-bug).
                   fc_current_lhs_flow: {FLOW,(1,23)=__flow}}
       FAIL_UNION 
         Trivial fail : MUSTno lemma found in both LHS and RHS nodes (do coercion)
       
 ]
Successful States:
,
Failed States:
[
 Label: [(69::,0 ); (69::,0 ); (68::,1 ); (68::,1 ); (65::,0 ); (65::,0 )]
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
                    (failure_code=213)  lg_585=lg & qs_587<=lg_585 & v_588<=qs_587 & sm_584=sm & v_588!=a & 
v_588!=a & v_588<a & v_588<a & sm_620=qs_587 & lg_621=lg_585 & 
sm_620<=lg_621 & p_896=p_589 & q_897=xright_894 & pl_586<=v_588 & 
B(sm_620,s_892,l_893,lg_621) & v_895=v_588 & (xright_894=null & 
s_892<=l_893 | xright_894!=null & s_892<=l_893) & (p_589=null & 
sm_584<=pl_586 | p_589!=null & sm_584<=pl_586) |-  v_895<=s_892 (may-bug).
                   fc_current_lhs_flow: {FLOW,(1,23)=__flow}}
       FAIL_UNION 
         Trivial fail : MUSTno lemma found in both LHS and RHS nodes (do coercion)
       ;
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
                    (failure_code=213)  sm_584=sm & sm_584<=pl_586 & pl_586<=v_588 & lg_585=lg & v_588!=a & 
v_588!=a & a<=v_588 & a<=v_588 & sm_640=sm_584 & lg_641=pl_586 & 
sm_640<=lg_641 & p_950=xleft_948 & q_951=q_590 & v_588<=qs_587 & 
B(sm_640,s_946,l_947,lg_641) & v_949=v_588 & (q_590=null & qs_587<=lg_585 | 
q_590!=null & qs_587<=lg_585) & (xleft_948=null & s_946<=l_947 | 
xleft_948!=null & s_946<=l_947) |-  l_947<=v_949 (may-bug).
                   fc_current_lhs_flow: {FLOW,(1,23)=__flow}}
       FAIL_UNION 
         Trivial fail : MUSTno lemma found in both LHS and RHS nodes (do coercion)
       
 ]
Successful States:
,
Failed States:
[
 Label: [(69::,0 ); (69::,0 ); (68::,1 ); (68::,1 ); (65::,0 ); (65::,0 )]
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
                    (failure_code=213)  lg_585=lg & qs_587<=lg_585 & v_588<=qs_587 & sm_584=sm & v_588!=a & 
v_588!=a & v_588<a & v_588<a & sm_620=qs_587 & lg_621=lg_585 & 
sm_620<=lg_621 & p_896=p_589 & q_897=xright_894 & pl_586<=v_588 & 
B(sm_620,s_892,l_893,lg_621) & v_895=v_588 & (xright_894=null & 
s_892<=l_893 | xright_894!=null & s_892<=l_893) & (p_589=null & 
sm_584<=pl_586 | p_589!=null & sm_584<=pl_586) |-  v_895<=s_892 (may-bug).
                   fc_current_lhs_flow: {FLOW,(1,23)=__flow}}
       FAIL_UNION 
         Trivial fail : MUSTno lemma found in both LHS and RHS nodes (do coercion)
       ;
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
                    (failure_code=213)  sm_584=sm & sm_584<=pl_586 & pl_586<=v_588 & lg_585=lg & v_588!=a & 
v_588!=a & a<=v_588 & a<=v_588 & sm_640=sm_584 & lg_641=pl_586 & 
sm_640<=lg_641 & p_950=xleft_948 & q_951=q_590 & v_588<=qs_587 & 
B(sm_640,s_946,l_947,lg_641) & v_949=v_588 & (q_590=null & qs_587<=lg_585 | 
q_590!=null & qs_587<=lg_585) & (xleft_948=null & s_946<=l_947 | 
xleft_948!=null & s_946<=l_947) |-  l_947<=v_949 (may-bug).
                   fc_current_lhs_flow: {FLOW,(1,23)=__flow}}
       FAIL_UNION 
         Trivial fail : MUSTno lemma found in both LHS and RHS nodes (do coercion)
       
 ]
Successful States:
,
Failed States:
[
 Label: [(69::,0 ); (69::,0 ); (68::,1 ); (68::,1 ); (65::,0 ); (65::,0 )]
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
                    (failure_code=213)  lg_585=lg & qs_587<=lg_585 & v_588<=qs_587 & sm_584=sm & v_588!=a & 
v_588!=a & v_588<a & v_588<a & sm_620=qs_587 & lg_621=lg_585 & 
sm_620<=lg_621 & p_896=p_589 & q_897=xright_894 & pl_586<=v_588 & 
B(sm_620,s_892,l_893,lg_621) & v_895=v_588 & (xright_894=null & 
s_892<=l_893 | xright_894!=null & s_892<=l_893) & (p_589=null & 
sm_584<=pl_586 | p_589!=null & sm_584<=pl_586) |-  v_895<=s_892 (may-bug).
                   fc_current_lhs_flow: {FLOW,(1,23)=__flow}}
       FAIL_UNION 
         Trivial fail : MUSTno lemma found in both LHS and RHS nodes (do coercion)
       ;
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
                    (failure_code=213)  sm_584=sm & sm_584<=pl_586 & pl_586<=v_588 & lg_585=lg & v_588!=a & 
v_588!=a & a<=v_588 & a<=v_588 & sm_640=sm_584 & lg_641=pl_586 & 
sm_640<=lg_641 & p_950=xleft_948 & q_951=q_590 & v_588<=qs_587 & 
B(sm_640,s_946,l_947,lg_641) & v_949=v_588 & (q_590=null & qs_587<=lg_585 | 
q_590!=null & qs_587<=lg_585) & (xleft_948=null & s_946<=l_947 | 
xleft_948!=null & s_946<=l_947) |-  l_947<=v_949 (may-bug).
                   fc_current_lhs_flow: {FLOW,(1,23)=__flow}}
       FAIL_UNION 
         Trivial fail : MUSTno lemma found in both LHS and RHS nodes (do coercion)
       
 ]
Successful States:
,
Failed States:
[
 Label: [(69::,0 ); (69::,0 ); (68::,1 ); (68::,1 ); (65::,0 ); (65::,0 )]
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
                    (failure_code=213)  lg_585=lg & qs_587<=lg_585 & v_588<=qs_587 & sm_584=sm & v_588!=a & 
v_588!=a & v_588<a & v_588<a & sm_620=qs_587 & lg_621=lg_585 & 
sm_620<=lg_621 & p_896=p_589 & q_897=xright_894 & pl_586<=v_588 & 
B(sm_620,s_892,l_893,lg_621) & v_895=v_588 & (xright_894=null & 
s_892<=l_893 | xright_894!=null & s_892<=l_893) & (p_589=null & 
sm_584<=pl_586 | p_589!=null & sm_584<=pl_586) |-  v_895<=s_892 (may-bug).
                   fc_current_lhs_flow: {FLOW,(1,23)=__flow}}
       FAIL_UNION 
         Trivial fail : MUSTno lemma found in both LHS and RHS nodes (do coercion)
       ;
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
                    (failure_code=213)  sm_584=sm & sm_584<=pl_586 & pl_586<=v_588 & lg_585=lg & v_588!=a & 
v_588!=a & a<=v_588 & a<=v_588 & sm_640=sm_584 & lg_641=pl_586 & 
sm_640<=lg_641 & p_950=xleft_948 & q_951=q_590 & v_588<=qs_587 & 
B(sm_640,s_946,l_947,lg_641) & v_949=v_588 & (q_590=null & qs_587<=lg_585 | 
q_590!=null & qs_587<=lg_585) & (xleft_948=null & s_946<=l_947 | 
xleft_948!=null & s_946<=l_947) |-  l_947<=v_949 (may-bug).
                   fc_current_lhs_flow: {FLOW,(1,23)=__flow}}
       FAIL_UNION 
         Trivial fail : MUSTno lemma found in both LHS and RHS nodes (do coercion)
       
 ]
Successful States:


Context of Verification Failure: File "bst-del.ss",Line:32,Col:12
Last Proving Location: File "bst-del.ss",Line:70,Col:6

ERROR: at bst-del.ss_32_12 
Message: Post condition cannot be derived by the system.
 
Procedure delete$node2~int FAIL-2

Exception Failure("Post condition cannot be derived by the system.") Occurred!

Error(s) detected when checking procedure delete$node2~int

Termination checking result:

Stop Omega... 528 invocations 
0 false contexts at: ()

Total verification time: 3.612224 second(s)
	Time spent in main process: 0.220013 second(s)
	Time spent in child processes: 3.392211 second(s)

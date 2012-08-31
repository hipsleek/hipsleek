Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure delete$node2~int... 
dprint: bst-del-b.ss:66: ctx:  List of Failesc Context: [FEC(0, 0, 4  [(149::,0 ); (149::,0 ); (144::,0 ); (144::,0 ); (141::,0 ); (141::,0 )];  [(149::,1 ); (149::,1 ); (144::,0 ); (144::,0 ); (141::,0 ); (141::,0 )];  [(145::,0 ); (145::,0 ); (144::,1 ); (144::,1 ); (141::,0 ); (141::,0 )];  [(145::,1 ); (145::,1 ); (144::,1 ); (144::,1 ); (141::,0 ); (141::,0 )])]

Successful States:
[
 Label: [(149::,0 ); (149::,0 ); (144::,0 ); (144::,0 ); (141::,0 ); (141::,0
          )]
 State:p_604::bst<sm_599,pl_601>@M[Orig] * q_605::bst<qs_602,lg_600>@M[Orig] * x'::node2<v_603,p_604,q_605>@M[Orig]&pl_601<=v_603 & v_603<=qs_602 & sm_599=sm & lg_600=lg & a'=a & x!=null & v_bool_36_545' & x!=null & v_bool_36_545' & v_603=a' & v_bool_41_541' & v_603=a' & v_bool_41_541' & q_605=null & v_bool_43_539' & q_605=null & v_bool_43_539' & x'=p_604&{FLOW,(20,21)=__norm}[]
       es_infer_vars/rel: [B]
       es_var_measures: MayLoop
;
 Label: [(149::,1 ); (149::,1 ); (144::,0 ); (144::,0 ); (141::,0 ); (141::,0
          )]
 State:EXISTS(s1_625,xright_34': p_604::bst<sm_599,pl_601>@M[Orig] * xright_34'::bst<s1_625,b>@M[Orig][LHSCase] * x'::node2<tmp_31',p_604,xright_34'>@M[Orig]&pl_601<=v_603 & v_603<=qs_602 & sm_599=sm & lg_600=lg & x'=x & a'=a & x'!=null & v_bool_36_545' & x'!=null & v_bool_36_545' & v_603=a' & v_bool_41_541' & v_603=a' & v_bool_41_541' & q_605!=null & !(v_bool_43_539') & q_605!=null & !(v_bool_43_539') & s=qs_602 & b=lg_600 & qs_602<=lg_600 & s<=tmp_31' & tmp_31'<=s1_625 & s<=b&{FLOW,(20,21)=__norm})[]
       es_infer_vars/rel: [B]
       es_var_measures: MayLoop
;
 Label: [(145::,0 ); (145::,0 ); (144::,1 ); (144::,1 ); (141::,0 ); (141::,0
          )]
 State:EXISTS(s_639,l_640,xright_34': p_604::bst<sm_599,pl_601>@M[Orig] * xright_34'::bst<s_639,l_640>@M[Orig][LHSCase] * x'::node2<v_603,p_604,xright_34'>@M[Orig]&pl_601<=v_603 & v_603<=qs_602 & sm_599=sm & lg_600=lg & x'=x & a'=a & x'!=null & v_bool_36_545' & x'!=null & v_bool_36_545' & v_603!=a' & !(v_bool_41_541') & v_603!=a' & !(v_bool_41_541') & v_603<a' & v_bool_60_540' & v_603<a' & v_bool_60_540' & sm_632=qs_602 & lg_633=lg_600 & qs_602<=lg_600 & sm_632<=s_639 & l_640<=lg_633 & B(sm_632,s_639,l_640,lg_633)&{FLOW,(20,21)=__norm})[]
       es_infer_vars/rel: [B]
       es_var_measures: MayLoop
;
 Label: [(145::,1 ); (145::,1 ); (144::,1 ); (144::,1 ); (141::,0 ); (141::,0
          )]
 State:EXISTS(s_648,l_649,xleft_33': q_605::bst<qs_602,lg_600>@M[Orig] * xleft_33'::bst<s_648,l_649>@M[Orig][LHSCase] * x'::node2<v_603,xleft_33',q_605>@M[Orig]&pl_601<=v_603 & v_603<=qs_602 & sm_599=sm & lg_600=lg & x'=x & a'=a & x'!=null & v_bool_36_545' & x'!=null & v_bool_36_545' & v_603!=a' & !(v_bool_41_541') & v_603!=a' & !(v_bool_41_541') & a'<=v_603 & !(v_bool_60_540') & a'<=v_603 & !(v_bool_60_540') & sm_641=sm_599 & lg_642=pl_601 & sm_599<=pl_601 & sm_641<=s_648 & l_649<=lg_642 & B(sm_641,s_648,l_649,lg_642)&{FLOW,(20,21)=__norm})[]
       es_infer_vars/rel: [B]
       es_var_measures: MayLoop

 ]

!!! REL :  B(sm,s,l,lg)
!!! POST:  l>=s & lg>=l & s=sm
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [B]
              EBase exists (Expl)(Impl)[sm; 
                    lg](ex)x::bst<sm,lg>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}[]
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                              EAssume 72::ref [x]
                                EXISTS(s,l: x'::bst<s,l>@M[Orig][LHSCase]&
                                sm<=s & l<=lg & B(sm,s,l,lg)&
                                {FLOW,(20,21)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[sm; 
                  lg](ex)x::bst<sm,lg>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}[]
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                            EAssume 72::ref [x]
                              EXISTS(s,l: x'::bst<s,l>@M[Orig][LHSCase]&
                              sm<=s & l<=lg & l>=s & lg>=l & s=sm&
                              {FLOW,(20,21)=__norm})[])
!!! NEW RELS:[ (sm=s & s<=l & l<=lg) --> B(sm,s,l,lg),
 (sm=s & s<=l & l<=lg) --> B(sm,s,l,lg),
 (sm=s & s<=l & l<=lg) --> B(sm,s,l,lg),
 (lg=l & sm=s & s<=l) --> B(sm,s,l,lg),
 (sm=s & lg=lg_633 & l_784=l & s<=sm_632 & sm_632<=s_783 & s_783<=l & 
  l<=lg_633 & B(sm_632,s_783,l_784,lg_633)) --> B(sm,s,l,lg),
 (lg=l & sm=sm_641 & s_816=s & sm_641<=s & s<=l_817 & l_817<=lg_642 & 
  lg_642<=l & B(sm_641,s_816,l_817,lg_642)) --> B(sm,s,l,lg),
 (sm=s & lg=l & s<=l) --> B(sm,s,l,lg)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete$node2~int SUCCESS

Termination checking result:

Stop Omega... 249 invocations 
0 false contexts at: ()

Total verification time: 0.88 second(s)
	Time spent in main process: 0.76 second(s)
	Time spent in child processes: 0.12 second(s)

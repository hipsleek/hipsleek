Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure delete$node2~int... 
dprint: bst-del-b.ss:66: ctx:  List of Failesc Context: [FEC(0, 0, 4  [(149::,0 ); (149::,0 ); (144::,0 ); (144::,0 ); (141::,0 ); (141::,0 )];  [(149::,1 ); (149::,1 ); (144::,0 ); (144::,0 ); (141::,0 ); (141::,0 )];  [(145::,0 ); (145::,0 ); (144::,1 ); (144::,1 ); (141::,0 ); (141::,0 )];  [(145::,1 ); (145::,1 ); (144::,1 ); (144::,1 ); (141::,0 ); (141::,0 )])]

Successful States:
[
 Label: [(149::,0 ); (149::,0 ); (144::,0 ); (144::,0 ); (141::,0 ); (141::,0
          )]
 State:p_618::bst<sm_613,pl_615>@M[Orig] * q_619::bst<qs_616,lg_614>@M[Orig] * x'::node2<v_617,p_618,q_619>@M[Orig]&pl_615<=v_617 & v_617<=qs_616 & sm_613=sm & lg_614=lg & a'=a & x!=null & v_bool_36_559' & x!=null & v_bool_36_559' & v_617=a' & v_bool_41_555' & v_617=a' & v_bool_41_555' & q_619=null & v_bool_43_553' & q_619=null & v_bool_43_553' & x'=p_618&{FLOW,(22,23)=__norm}[]
       es_infer_vars/rel: [B]
       es_var_measures: MayLoop
;
 Label: [(149::,1 ); (149::,1 ); (144::,0 ); (144::,0 ); (141::,0 ); (141::,0
          )]
 State:EXISTS(s1_639,xright_26': p_618::bst<sm_613,pl_615>@M[Orig] * xright_26'::bst<s1_639,b>@M[Orig][LHSCase] * x'::node2<tmp_23',p_618,xright_26'>@M[Orig]&pl_615<=v_617 & v_617<=qs_616 & sm_613=sm & lg_614=lg & x'=x & a'=a & x'!=null & v_bool_36_559' & x'!=null & v_bool_36_559' & v_617=a' & v_bool_41_555' & v_617=a' & v_bool_41_555' & q_619!=null & !(v_bool_43_553') & q_619!=null & !(v_bool_43_553') & s=qs_616 & b=lg_614 & qs_616<=lg_614 & s<=tmp_23' & tmp_23'<=s1_639 & s<=b&{FLOW,(22,23)=__norm})[]
       es_infer_vars/rel: [B]
       es_var_measures: MayLoop
;
 Label: [(145::,0 ); (145::,0 ); (144::,1 ); (144::,1 ); (141::,0 ); (141::,0
          )]
 State:EXISTS(s_653,l_654,xright_26': p_618::bst<sm_613,pl_615>@M[Orig] * xright_26'::bst<s_653,l_654>@M[Orig][LHSCase] * x'::node2<v_617,p_618,xright_26'>@M[Orig]&pl_615<=v_617 & v_617<=qs_616 & sm_613=sm & lg_614=lg & x'=x & a'=a & x'!=null & v_bool_36_559' & x'!=null & v_bool_36_559' & v_617!=a' & !(v_bool_41_555') & v_617!=a' & !(v_bool_41_555') & v_617<a' & v_bool_60_554' & v_617<a' & v_bool_60_554' & sm_646=qs_616 & lg_647=lg_614 & qs_616<=lg_614 & sm_646<=s_653 & l_654<=lg_647 & B(sm_646,s_653,l_654,lg_647)&{FLOW,(22,23)=__norm})[]
       es_infer_vars/rel: [B]
       es_var_measures: MayLoop
;
 Label: [(145::,1 ); (145::,1 ); (144::,1 ); (144::,1 ); (141::,0 ); (141::,0
          )]
 State:EXISTS(s_662,l_663,xleft_25': q_619::bst<qs_616,lg_614>@M[Orig] * xleft_25'::bst<s_662,l_663>@M[Orig][LHSCase] * x'::node2<v_617,xleft_25',q_619>@M[Orig]&pl_615<=v_617 & v_617<=qs_616 & sm_613=sm & lg_614=lg & x'=x & a'=a & x'!=null & v_bool_36_559' & x'!=null & v_bool_36_559' & v_617!=a' & !(v_bool_41_555') & v_617!=a' & !(v_bool_41_555') & a'<=v_617 & !(v_bool_60_554') & a'<=v_617 & !(v_bool_60_554') & sm_655=sm_613 & lg_656=pl_615 & sm_613<=pl_615 & sm_655<=s_662 & l_663<=lg_656 & B(sm_655,s_662,l_663,lg_656)&{FLOW,(22,23)=__norm})[]
       es_infer_vars/rel: [B]
       es_var_measures: MayLoop

 ]

!!! REL :  B(sm,s,l,lg)
!!! POST:  l>=s & lg>=l & s=sm
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [B]
              EBase exists (Expl)(Impl)[sm; 
                    lg](ex)x::bst<sm,lg>@M[Orig][LHSCase]&true&
                    {FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 72::ref [x]
                                EXISTS(s,l: x'::bst<s,l>@M[Orig][LHSCase]&
                                sm<=s & l<=lg & B(sm,s,l,lg)&
                                {FLOW,(22,23)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[sm; 
                  lg](ex)x::bst<sm,lg>@M[Orig][LHSCase]&true&
                  {FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 72::ref [x]
                              EXISTS(s,l: x'::bst<s,l>@M[Orig][LHSCase]&
                              sm<=s & l<=lg & l>=s & lg>=l & s=sm&
                              {FLOW,(22,23)=__norm})[])
!!! NEW RELS:[ (sm=s & s<=l & l<=lg) --> B(sm,s,l,lg),
 (sm=s & s<=l & l<=lg) --> B(sm,s,l,lg),
 (sm=s & s<=l & l<=lg) --> B(sm,s,l,lg),
 (lg=l & sm=s & s<=l) --> B(sm,s,l,lg),
 (sm=s & lg=lg_647 & l_800=l & s<=sm_646 & sm_646<=s_799 & s_799<=l & 
  l<=lg_647 & B(sm_646,s_799,l_800,lg_647)) --> B(sm,s,l,lg),
 (lg=l & sm=sm_655 & s_832=s & sm_655<=s & s<=l_833 & l_833<=lg_656 & 
  lg_656<=l & B(sm_655,s_832,l_833,lg_656)) --> B(sm,s,l,lg),
 (sm=s & lg=l & s<=l) --> B(sm,s,l,lg)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete$node2~int SUCCESS

Termination checking result:

Stop Omega... 234 invocations 
0 false contexts at: ()

Total verification time: 0.94 second(s)
	Time spent in main process: 0.82 second(s)
	Time spent in child processes: 0.12 second(s)

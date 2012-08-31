Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure delete$node2~int... 
dprint: bst-del-c.ss:66: ctx:  List of Failesc Context: [FEC(0, 0, 4  [(149::,0 ); (149::,0 ); (144::,0 ); (144::,0 ); (141::,0 ); (141::,0 )];  [(149::,1 ); (149::,1 ); (144::,0 ); (144::,0 ); (141::,0 ); (141::,0 )];  [(145::,0 ); (145::,0 ); (144::,1 ); (144::,1 ); (141::,0 ); (141::,0 )];  [(145::,1 ); (145::,1 ); (144::,1 ); (144::,1 ); (141::,0 ); (141::,0 )])]

Successful States:
[
 Label: [(149::,0 ); (149::,0 ); (144::,0 ); (144::,0 ); (141::,0 ); (141::,0
          )]
 State:p_601::bst<sm_596,pl_598>@M[Orig] * q_602::bst<qs_599,lg_597>@M[Orig] * x'::node2<v_600,p_601,q_602>@M[Orig]&pl_598<=v_600 & v_600<=qs_599 & sm_596=sm & lg_597=lg & a'=a & x!=null & v_bool_36_542' & x!=null & v_bool_36_542' & v_600=a' & v_bool_41_538' & v_600=a' & v_bool_41_538' & q_602=null & v_bool_43_536' & q_602=null & v_bool_43_536' & x'=p_601&{FLOW,(20,21)=__norm}[]
       es_infer_vars/rel: [B]
       es_var_measures: MayLoop
;
 Label: [(149::,1 ); (149::,1 ); (144::,0 ); (144::,0 ); (141::,0 ); (141::,0
          )]
 State:EXISTS(s1_622,xright_34': p_601::bst<sm_596,pl_598>@M[Orig] * xright_34'::bst<s1_622,b>@M[Orig][LHSCase] * x'::node2<tmp_31',p_601,xright_34'>@M[Orig]&pl_598<=v_600 & v_600<=qs_599 & sm_596=sm & lg_597=lg & x'=x & a'=a & x'!=null & v_bool_36_542' & x'!=null & v_bool_36_542' & v_600=a' & v_bool_41_538' & v_600=a' & v_bool_41_538' & q_602!=null & !(v_bool_43_536') & q_602!=null & !(v_bool_43_536') & s=qs_599 & b=lg_597 & qs_599<=lg_597 & s<=tmp_31' & tmp_31'<=s1_622 & s<=b&{FLOW,(20,21)=__norm})[]
       es_infer_vars/rel: [B]
       es_var_measures: MayLoop
;
 Label: [(145::,0 ); (145::,0 ); (144::,1 ); (144::,1 ); (141::,0 ); (141::,0
          )]
 State:EXISTS(l_636,s_637,xright_34': p_601::bst<sm_596,pl_598>@M[Orig] * xright_34'::bst<s_637,l_636>@M[Orig][LHSCase] * x'::node2<v_600,p_601,xright_34'>@M[Orig]&pl_598<=v_600 & v_600<=qs_599 & sm_596=sm & lg_597=lg & x'=x & a'=a & x'!=null & v_bool_36_542' & x'!=null & v_bool_36_542' & v_600!=a' & !(v_bool_41_538') & v_600!=a' & !(v_bool_41_538') & v_600<a' & v_bool_60_537' & v_600<a' & v_bool_60_537' & sm_629=qs_599 & lg_630=lg_597 & qs_599<=lg_597 & l_636<=lg_630 & B(s_637,sm_629)&{FLOW,(20,21)=__norm})[]
       es_infer_vars/rel: [B]
       es_var_measures: MayLoop
;
 Label: [(145::,1 ); (145::,1 ); (144::,1 ); (144::,1 ); (141::,0 ); (141::,0
          )]
 State:EXISTS(l_645,s_646,xleft_33': q_602::bst<qs_599,lg_597>@M[Orig] * xleft_33'::bst<s_646,l_645>@M[Orig][LHSCase] * x'::node2<v_600,xleft_33',q_602>@M[Orig]&pl_598<=v_600 & v_600<=qs_599 & sm_596=sm & lg_597=lg & x'=x & a'=a & x'!=null & v_bool_36_542' & x'!=null & v_bool_36_542' & v_600!=a' & !(v_bool_41_538') & v_600!=a' & !(v_bool_41_538') & a'<=v_600 & !(v_bool_60_537') & a'<=v_600 & !(v_bool_60_537') & sm_638=sm_596 & lg_639=pl_598 & sm_596<=pl_598 & l_645<=lg_639 & B(s_646,sm_638)&{FLOW,(20,21)=__norm})[]
       es_infer_vars/rel: [B]
       es_var_measures: MayLoop

 ]

!!! REL :  B(s,sm)
!!! POST:  s=sm
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [B]
              EBase exists (Expl)(Impl)[sm; 
                    lg](ex)x::bst<sm,lg>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}[]
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                              EAssume 72::ref [x]
                                EXISTS(l,s: x'::bst<s,l>@M[Orig][LHSCase]&
                                l<=lg & B(s,sm)&{FLOW,(20,21)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[sm; 
                  lg](ex)x::bst<sm,lg>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}[]
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                            EAssume 72::ref [x]
                              EXISTS(l,s: x'::bst<s,l>@M[Orig][LHSCase]&
                              l<=lg & s=sm&{FLOW,(20,21)=__norm})[])
!!! NEW RELS:[ (sm=s & s<=sm_629 & B(s_781,sm_629)) --> B(s,sm),
 (sm=sm_638 & s_814=s & B(s_814,sm_638)) --> B(s,sm),
 (sm=s) --> B(s,sm)]
!!! NEW ASSUME:[ RELASS [B]: ( B(s_781,sm_629)) -->  sm_629<=s_781]
!!! NEW RANK:[]
Procedure delete$node2~int SUCCESS

Termination checking result:

Stop Omega... 255 invocations 
0 false contexts at: ()

Total verification time: 1.94 second(s)
	Time spent in main process: 0.76 second(s)
	Time spent in child processes: 1.18 second(s)

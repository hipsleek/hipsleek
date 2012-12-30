Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure delete$node2~int... 
dprint: bst-del-c.ss:66: ctx:  List of Failesc Context: [FEC(0, 0, 4  [(149::,0 ); (149::,0 ); (144::,0 ); (144::,0 ); (141::,0 ); (141::,0 )];  [(149::,1 ); (149::,1 ); (144::,0 ); (144::,0 ); (141::,0 ); (141::,0 )];  [(145::,0 ); (145::,0 ); (144::,1 ); (144::,1 ); (141::,0 ); (141::,0 )];  [(145::,1 ); (145::,1 ); (144::,1 ); (144::,1 ); (141::,0 ); (141::,0 )])]

Successful States:
[
 Label: [(149::,0 ); (149::,0 ); (144::,0 ); (144::,0 ); (141::,0 ); (141::,0
          )]
 State:p_615::bst<sm_610,pl_612>@M[Orig] * q_616::bst<qs_613,lg_611>@M[Orig] * x'::node2<v_614,p_615,q_616>@M[Orig]&pl_612<=v_614 & v_614<=qs_613 & sm_610=sm & lg_611=lg & a'=a & x!=null & v_bool_36_556' & x!=null & v_bool_36_556' & v_614=a' & v_bool_41_552' & v_614=a' & v_bool_41_552' & q_616=null & v_bool_43_550' & q_616=null & v_bool_43_550' & x'=p_615&{FLOW,(22,23)=__norm}[]
       es_infer_vars/rel: [B]
       es_var_measures: MayLoop
;
 Label: [(149::,1 ); (149::,1 ); (144::,0 ); (144::,0 ); (141::,0 ); (141::,0
          )]
 State:EXISTS(s1_636,xright_26': p_615::bst<sm_610,pl_612>@M[Orig] * xright_26'::bst<s1_636,b>@M[Orig][LHSCase] * x'::node2<tmp_23',p_615,xright_26'>@M[Orig]&pl_612<=v_614 & v_614<=qs_613 & sm_610=sm & lg_611=lg & x'=x & a'=a & x'!=null & v_bool_36_556' & x'!=null & v_bool_36_556' & v_614=a' & v_bool_41_552' & v_614=a' & v_bool_41_552' & q_616!=null & !(v_bool_43_550') & q_616!=null & !(v_bool_43_550') & s=qs_613 & b=lg_611 & qs_613<=lg_611 & s<=tmp_23' & tmp_23'<=s1_636 & s<=b&{FLOW,(22,23)=__norm})[]
       es_infer_vars/rel: [B]
       es_var_measures: MayLoop
;
 Label: [(145::,0 ); (145::,0 ); (144::,1 ); (144::,1 ); (141::,0 ); (141::,0
          )]
 State:EXISTS(l_650,s_651,xright_26': p_615::bst<sm_610,pl_612>@M[Orig] * xright_26'::bst<s_651,l_650>@M[Orig][LHSCase] * x'::node2<v_614,p_615,xright_26'>@M[Orig]&pl_612<=v_614 & v_614<=qs_613 & sm_610=sm & lg_611=lg & x'=x & a'=a & x'!=null & v_bool_36_556' & x'!=null & v_bool_36_556' & v_614!=a' & !(v_bool_41_552') & v_614!=a' & !(v_bool_41_552') & v_614<a' & v_bool_60_551' & v_614<a' & v_bool_60_551' & sm_643=qs_613 & lg_644=lg_611 & qs_613<=lg_611 & l_650<=lg_644 & B(s_651,sm_643)&{FLOW,(22,23)=__norm})[]
       es_infer_vars/rel: [B]
       es_var_measures: MayLoop
;
 Label: [(145::,1 ); (145::,1 ); (144::,1 ); (144::,1 ); (141::,0 ); (141::,0
          )]
 State:EXISTS(l_659,s_660,xleft_25': q_616::bst<qs_613,lg_611>@M[Orig] * xleft_25'::bst<s_660,l_659>@M[Orig][LHSCase] * x'::node2<v_614,xleft_25',q_616>@M[Orig]&pl_612<=v_614 & v_614<=qs_613 & sm_610=sm & lg_611=lg & x'=x & a'=a & x'!=null & v_bool_36_556' & x'!=null & v_bool_36_556' & v_614!=a' & !(v_bool_41_552') & v_614!=a' & !(v_bool_41_552') & a'<=v_614 & !(v_bool_60_551') & a'<=v_614 & !(v_bool_60_551') & sm_652=sm_610 & lg_653=pl_612 & sm_610<=pl_612 & l_659<=lg_653 & B(s_660,sm_652)&{FLOW,(22,23)=__norm})[]
       es_infer_vars/rel: [B]
       es_var_measures: MayLoop

 ]

!!! REL :  B(s,sm)
!!! POST:  s=sm
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [B]
              EBase exists (Expl)(Impl)[sm; 
                    lg](ex)x::bst<sm,lg>@M[Orig][LHSCase]&true&
                    {FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 72::ref [x]
                                EXISTS(l,s: x'::bst<s,l>@M[Orig][LHSCase]&
                                l<=lg & B(s,sm)&{FLOW,(22,23)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[sm; 
                  lg](ex)x::bst<sm,lg>@M[Orig][LHSCase]&true&
                  {FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 72::ref [x]
                              EXISTS(l,s: x'::bst<s,l>@M[Orig][LHSCase]&
                              l<=lg & s=sm&{FLOW,(22,23)=__norm})[])
!!! NEW RELS:[ (sm=s & s<=sm_643 & B(s_797,sm_643)) --> B(s,sm),
 (sm=sm_652 & s_830=s & B(s_830,sm_652)) --> B(s,sm),
 (sm=s) --> B(s,sm)]
!!! NEW ASSUME:[ RELASS [B]: ( B(s_797,sm_643)) -->  sm_643<=s_797]
!!! NEW RANK:[]
Procedure delete$node2~int SUCCESS

Termination checking result:

Stop Omega... 243 invocations 
0 false contexts at: ()

Total verification time: 1.98 second(s)
	Time spent in main process: 0.81 second(s)
	Time spent in child processes: 1.17 second(s)

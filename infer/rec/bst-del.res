Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure delete$node2~int... 
dprint: bst-del.ss:67: ctx:  List of Failesc Context: [FEC(0, 0, 4  [(149::,0 ); (149::,0 ); (144::,0 ); (144::,0 ); (141::,0 ); (141::,0 )];  [(149::,1 ); (149::,1 ); (144::,0 ); (144::,0 ); (141::,0 ); (141::,0 )];  [(145::,0 ); (145::,0 ); (144::,1 ); (144::,1 ); (141::,0 ); (141::,0 )];  [(145::,1 ); (145::,1 ); (144::,1 ); (144::,1 ); (141::,0 ); (141::,0 )])]

Successful States:
[
 Label: [(149::,0 ); (149::,0 ); (144::,0 ); (144::,0 ); (141::,0 ); (141::,0
          )]
 State:p_616::bst<sm_611,pl_613>@M[Orig] * q_617::bst<qs_614,lg_612>@M[Orig] * x'::node2<v_615,p_616,q_617>@M[Orig]&pl_613<=v_615 & v_615<=qs_614 & sm_611=sm & lg_612=lg & a'=a & x!=null & v_bool_37_557' & x!=null & v_bool_37_557' & v_615=a' & v_bool_42_553' & v_615=a' & v_bool_42_553' & q_617=null & v_bool_44_551' & q_617=null & v_bool_44_551' & x'=p_616&{FLOW,(22,23)=__norm}[]d
       es_infer_vars/rel: [B]
       es_var_measures: MayLoop
;
 Label: [(149::,1 ); (149::,1 ); (144::,0 ); (144::,0 ); (141::,0 ); (141::,0
          )]
 State:EXISTS(s1_637,xright_26': p_616::bst<sm_611,pl_613>@M[Orig] * xright_26'::bst<s1_637,b>@M[Orig][LHSCase] * x'::node2<tmp_23',p_616,xright_26'>@M[Orig]&pl_613<=v_615 & v_615<=qs_614 & sm_611=sm & lg_612=lg & x'=x & a'=a & x'!=null & v_bool_37_557' & x'!=null & v_bool_37_557' & v_615=a' & v_bool_42_553' & v_615=a' & v_bool_42_553' & q_617!=null & !(v_bool_44_551') & q_617!=null & !(v_bool_44_551') & s=qs_614 & b=lg_612 & qs_614<=lg_612 & s<=tmp_23' & tmp_23'<=s1_637 & s<=b&{FLOW,(22,23)=__norm})[]
       es_infer_vars/rel: [B]
       es_var_measures: MayLoop
;
 Label: [(145::,0 ); (145::,0 ); (144::,1 ); (144::,1 ); (141::,0 ); (141::,0
          )]
 State:EXISTS(s_651,l_652,xright_26': p_616::bst<sm_611,pl_613>@M[Orig] * xright_26'::bst<s_651,l_652>@M[Orig][LHSCase] * x'::node2<v_615,p_616,xright_26'>@M[Orig]&pl_613<=v_615 & v_615<=qs_614 & sm_611=sm & lg_612=lg & x'=x & a'=a & x'!=null & v_bool_37_557' & x'!=null & v_bool_37_557' & v_615!=a' & !(v_bool_42_553') & v_615!=a' & !(v_bool_42_553') & v_615<a' & v_bool_61_552' & v_615<a' & v_bool_61_552' & sm_644=qs_614 & lg_645=lg_612 & qs_614<=lg_612 & B(sm_644,s_651,l_652,lg_645)&{FLOW,(22,23)=__norm})[]
       es_infer_vars/rel: [B]
       es_var_measures: MayLoop
;
 Label: [(145::,1 ); (145::,1 ); (144::,1 ); (144::,1 ); (141::,0 ); (141::,0
          )]
 State:EXISTS(s_660,l_661,xleft_25': q_617::bst<qs_614,lg_612>@M[Orig] * xleft_25'::bst<s_660,l_661>@M[Orig][LHSCase] * x'::node2<v_615,xleft_25',q_617>@M[Orig]&pl_613<=v_615 & v_615<=qs_614 & sm_611=sm & lg_612=lg & x'=x & a'=a & x'!=null & v_bool_37_557' & x'!=null & v_bool_37_557' & v_615!=a' & !(v_bool_42_553') & v_615!=a' & !(v_bool_42_553') & a'<=v_615 & !(v_bool_61_552') & a'<=v_615 & !(v_bool_61_552') & sm_653=sm_611 & lg_654=pl_613 & sm_611<=pl_613 & B(sm_653,s_660,l_661,lg_654)&{FLOW,(22,23)=__norm})[]
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
                                B(sm,s,l,lg)&{FLOW,(22,23)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[sm; 
                  lg](ex)x::bst<sm,lg>@M[Orig][LHSCase]&true&
                  {FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 72::ref [x]
                              EXISTS(s,l: x'::bst<s,l>@M[Orig][LHSCase]&
                              l>=s & lg>=l & s=sm&{FLOW,(22,23)=__norm})[])
!!! NEW RELS:[ (sm=s & s<=l & l<=lg) --> B(sm,s,l,lg),
 (sm=s & s<=l & l<=lg) --> B(sm,s,l,lg),
 (sm=s & s<=l & l<=lg) --> B(sm,s,l,lg),
 (lg=l & sm=s & s<=l) --> B(sm,s,l,lg),
 (sm=s & lg=lg_645 & l_798=l & s<=sm_644 & sm_644<=lg_645 & s_797<=l & 
  B(sm_644,s_797,l_798,lg_645)) --> B(sm,s,l,lg),
 (lg=l & sm=sm_653 & s_830=s & sm_653<=lg_654 & lg_654<=l & s<=l_831 & 
  B(sm_653,s_830,l_831,lg_654)) --> B(sm,s,l,lg),
 (sm=s & lg=l & s<=l) --> B(sm,s,l,lg)]
!!! NEW ASSUME:[ RELASS [B]: ( B(sm_644,s_797,l_798,lg_645)) -->  sm_644<=s_797 | lg_645<sm_644 & s_797<sm_644 | l_798<s_797 & s_797<sm_644 & 
sm_644<=lg_645,
 RELASS [B]: ( B(sm_653,s_830,l_831,lg_654)) -->  lg_654<sm_653 | sm_653<=lg_654 & l_831<s_830 | s_830<=l_831 & 
l_831<=lg_654 & sm_653<=lg_654]
!!! NEW RANK:[]
Procedure delete$node2~int SUCCESS

Termination checking result:

Stop Omega... 250 invocations 
0 false contexts at: ()

Total verification time: 2.72 second(s)
	Time spent in main process: 0.81 second(s)
	Time spent in child processes: 1.91 second(s)

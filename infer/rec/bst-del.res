Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure delete$node2~int... 
dprint: bst-del.ss:67: ctx:  List of Failesc Context: [FEC(0, 0, 4  [(149::,0 ); (149::,0 ); (144::,0 ); (144::,0 ); (141::,0 ); (141::,0 )];  [(149::,1 ); (149::,1 ); (144::,0 ); (144::,0 ); (141::,0 ); (141::,0 )];  [(145::,0 ); (145::,0 ); (144::,1 ); (144::,1 ); (141::,0 ); (141::,0 )];  [(145::,1 ); (145::,1 ); (144::,1 ); (144::,1 ); (141::,0 ); (141::,0 )])]

Successful States:
[
 Label: [(149::,0 ); (149::,0 ); (144::,0 ); (144::,0 ); (141::,0 ); (141::,0
          )]
 State:p_602::bst<sm_597,pl_599>@M[Orig] * q_603::bst<qs_600,lg_598>@M[Orig] * x'::node2<v_601,p_602,q_603>@M[Orig]&pl_599<=v_601 & v_601<=qs_600 & sm_597=sm & lg_598=lg & a'=a & x!=null & v_bool_37_543' & x!=null & v_bool_37_543' & v_601=a' & v_bool_42_539' & v_601=a' & v_bool_42_539' & q_603=null & v_bool_44_537' & q_603=null & v_bool_44_537' & x'=p_602&{FLOW,(20,21)=__norm}[]
       es_infer_vars/rel: [B]
       es_var_measures: MayLoop
;
 Label: [(149::,1 ); (149::,1 ); (144::,0 ); (144::,0 ); (141::,0 ); (141::,0
          )]
 State:EXISTS(s1_623,xright_34': p_602::bst<sm_597,pl_599>@M[Orig] * xright_34'::bst<s1_623,b>@M[Orig][LHSCase] * x'::node2<tmp_31',p_602,xright_34'>@M[Orig]&pl_599<=v_601 & v_601<=qs_600 & sm_597=sm & lg_598=lg & x'=x & a'=a & x'!=null & v_bool_37_543' & x'!=null & v_bool_37_543' & v_601=a' & v_bool_42_539' & v_601=a' & v_bool_42_539' & q_603!=null & !(v_bool_44_537') & q_603!=null & !(v_bool_44_537') & s=qs_600 & b=lg_598 & qs_600<=lg_598 & s<=tmp_31' & tmp_31'<=s1_623 & s<=b&{FLOW,(20,21)=__norm})[]
       es_infer_vars/rel: [B]
       es_var_measures: MayLoop
;
 Label: [(145::,0 ); (145::,0 ); (144::,1 ); (144::,1 ); (141::,0 ); (141::,0
          )]
 State:EXISTS(s_637,l_638,xright_34': p_602::bst<sm_597,pl_599>@M[Orig] * xright_34'::bst<s_637,l_638>@M[Orig][LHSCase] * x'::node2<v_601,p_602,xright_34'>@M[Orig]&pl_599<=v_601 & v_601<=qs_600 & sm_597=sm & lg_598=lg & x'=x & a'=a & x'!=null & v_bool_37_543' & x'!=null & v_bool_37_543' & v_601!=a' & !(v_bool_42_539') & v_601!=a' & !(v_bool_42_539') & v_601<a' & v_bool_61_538' & v_601<a' & v_bool_61_538' & sm_630=qs_600 & lg_631=lg_598 & qs_600<=lg_598 & B(sm_630,s_637,l_638,lg_631)&{FLOW,(20,21)=__norm})[]
       es_infer_vars/rel: [B]
       es_var_measures: MayLoop
;
 Label: [(145::,1 ); (145::,1 ); (144::,1 ); (144::,1 ); (141::,0 ); (141::,0
          )]
 State:EXISTS(s_646,l_647,xleft_33': q_603::bst<qs_600,lg_598>@M[Orig] * xleft_33'::bst<s_646,l_647>@M[Orig][LHSCase] * x'::node2<v_601,xleft_33',q_603>@M[Orig]&pl_599<=v_601 & v_601<=qs_600 & sm_597=sm & lg_598=lg & x'=x & a'=a & x'!=null & v_bool_37_543' & x'!=null & v_bool_37_543' & v_601!=a' & !(v_bool_42_539') & v_601!=a' & !(v_bool_42_539') & a'<=v_601 & !(v_bool_61_538') & a'<=v_601 & !(v_bool_61_538') & sm_639=sm_597 & lg_640=pl_599 & sm_597<=pl_599 & B(sm_639,s_646,l_647,lg_640)&{FLOW,(20,21)=__norm})[]
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
                                B(sm,s,l,lg)&{FLOW,(20,21)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[sm; 
                  lg](ex)x::bst<sm,lg>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}[]
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                            EAssume 72::ref [x]
                              EXISTS(s,l: x'::bst<s,l>@M[Orig][LHSCase]&
                              l>=s & lg>=l & s=sm&{FLOW,(20,21)=__norm})[])
!!! NEW RELS:[ (sm=s & s<=l & l<=lg) --> B(sm,s,l,lg),
 (sm=s & s<=l & l<=lg) --> B(sm,s,l,lg),
 (sm=s & s<=l & l<=lg) --> B(sm,s,l,lg),
 (lg=l & sm=s & s<=l) --> B(sm,s,l,lg),
 (sm=s & lg=lg_631 & l_782=l & s<=sm_630 & sm_630<=lg_631 & s_781<=l & 
  B(sm_630,s_781,l_782,lg_631)) --> B(sm,s,l,lg),
 (lg=l & sm=sm_639 & s_814=s & sm_639<=lg_640 & lg_640<=l & s<=l_815 & 
  B(sm_639,s_814,l_815,lg_640)) --> B(sm,s,l,lg),
 (sm=s & lg=l & s<=l) --> B(sm,s,l,lg)]
!!! NEW ASSUME:[ RELASS [B]: ( B(sm_630,s_781,l_782,lg_631)) -->  sm_630<=s_781 | lg_631<sm_630 & s_781<sm_630 | l_782<s_781 & s_781<sm_630 & 
sm_630<=lg_631,
 RELASS [B]: ( B(sm_639,s_814,l_815,lg_640)) -->  lg_640<sm_639 | sm_639<=lg_640 & l_815<s_814 | s_814<=l_815 & 
l_815<=lg_640 & sm_639<=lg_640]
!!! NEW RANK:[]
Procedure delete$node2~int SUCCESS

Termination checking result:

Stop Omega... 257 invocations 
0 false contexts at: ()

Total verification time: 2.67 second(s)
	Time spent in main process: 0.77 second(s)
	Time spent in child processes: 1.9 second(s)

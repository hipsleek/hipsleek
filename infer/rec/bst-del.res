
Processing file "bst-del.ss"
Parsing bst-del.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
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

!!! REL :  B(sm,s,l,lg)
!!! POST:  l>=s & lg>=l & s=sm
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [B]
              EBase exists (Expl)(Impl)[sm; 
                    lg](ex)x::bst<sm,lg>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 2::ref [x]
                                EXISTS(s,l: x'::bst<s,l>@M[Orig][LHSCase]&
                                B(sm,s,l,lg)&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[sm; 
                  lg](ex)x::bst<sm,lg>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 2::ref [x]
                              EXISTS(s_1005,
                              l_1006: x'::bst<s_1005,l_1006>@M[Orig][LHSCase]&
                              l_1006>=s_1005 & lg>=l_1006 & s_1005=sm & 
                              sm<=lg&{FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (sm=s & s<=l & l<=lg) --> B(sm,s,l,lg),
 (sm=s & s<=l & l<=lg) --> B(sm,s,l,lg),
 (sm=s & s<=l & l<=lg) --> B(sm,s,l,lg),
 (lg=l & sm=s & s<=l) --> B(sm,s,l,lg),
 (sm=s & lg=lg_621 & l_893=l & s<=sm_620 & sm_620<=lg_621 & s_892<=l & 
  B(sm_620,s_892,l_893,lg_621)) --> B(sm,s,l,lg),
 (lg=l & sm=sm_640 & s_947=s & sm_640<=lg_641 & lg_641<=l & s<=l_948 & 
  B(sm_640,s_947,l_948,lg_641)) --> B(sm,s,l,lg),
 (sm=s & lg=l & s<=l) --> B(sm,s,l,lg)]
!!! NEW ASSUME:[ RELASS [B]: ( B(sm_620,s_892,l_893,lg_621)) -->  lg_621<sm_620 | sm_620<=lg_621 & sm_620<=s_892 | l_893<s_892 & 
s_892<sm_620 & sm_620<=lg_621,
 RELASS [B]: ( B(sm_640,s_947,l_948,lg_641)) -->  l_948<s_947 | lg_641<sm_640 & s_947<=l_948 | s_947<=l_948 & l_948<=lg_641 & 
sm_640<=lg_641]
!!! NEW RANK:[]
Procedure delete$node2~int SUCCESS

Termination checking result:

Stop Omega... 350 invocations 
0 false contexts at: ()

Total verification time: 1.32 second(s)
	Time spent in main process: 0.15 second(s)
	Time spent in child processes: 1.17 second(s)

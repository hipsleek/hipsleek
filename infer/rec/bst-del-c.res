
Processing file "bst-del-c.ss"
Parsing bst-del-c.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure delete$node2~int... 
dprint: bst-del-c.ss:66: ctx:  List of Failesc Context: [FEC(0, 0, 4  [(73::,0 ); (73::,0 ); (68::,0 ); (68::,0 ); (65::,0 ); (65::,0 )];  [(73::,1 ); (73::,1 ); (68::,0 ); (68::,0 ); (65::,0 ); (65::,0 )];  [(69::,0 ); (69::,0 ); (68::,1 ); (68::,1 ); (65::,0 ); (65::,0 )];  [(69::,1 ); (69::,1 ); (68::,1 ); (68::,1 ); (65::,0 ); (65::,0 )])]

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
 State:EXISTS(l_637,s_638,xright_34': p_588::bst<sm_583,pl_585>@M[Orig] * xright_34'::bst<s_638,l_637>@M[Orig][LHSCase] * x'::node2<v_587,p_588,xright_34'>@M[Orig]&pl_585<=v_587 & v_587<=qs_586 & sm_583=sm & lg_584=lg & x'=x & a'=a & x'!=null & v_bool_36_529' & x'!=null & v_bool_36_529' & v_587!=a' & 163::!(v_bool_41_525') & v_587!=a' & !(v_bool_41_525') & v_587<a' & v_bool_60_524' & v_587<a' & v_bool_60_524' & sm_619=qs_586 & lg_620=lg_584 & qs_586<=lg_584 & l_637<=lg_620 & B(s_638,sm_619) & sm_619<=lg_620&{FLOW,(20,21)=__norm})
       es_infer_vars/rel: [B]
       es_var_measures: MayLoop;
 Label: [(69::,1 ); (69::,1 ); (68::,1 ); (68::,1 ); (65::,0 ); (65::,0 )]
 State:EXISTS(l_657,s_658,xleft_33': q_589::bst<qs_586,lg_584>@M[Orig] * xleft_33'::bst<s_658,l_657>@M[Orig][LHSCase] * x'::node2<v_587,xleft_33',q_589>@M[Orig]&pl_585<=v_587 & v_587<=qs_586 & sm_583=sm & lg_584=lg & x'=x & a'=a & x'!=null & v_bool_36_529' & x'!=null & v_bool_36_529' & v_587!=a' & 163::!(v_bool_41_525') & v_587!=a' & !(v_bool_41_525') & a'<=v_587 & 198::!(v_bool_60_524') & a'<=v_587 & !(v_bool_60_524') & sm_639=sm_583 & lg_640=pl_585 & sm_583<=pl_585 & l_657<=lg_640 & B(s_658,sm_639) & sm_639<=lg_640&{FLOW,(20,21)=__norm})
       es_infer_vars/rel: [B]
       es_var_measures: MayLoop
 ]

!!! REL :  B(s,sm)
!!! POST:  s=sm
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [B]
              EBase exists (Expl)(Impl)[sm; 
                    lg](ex)x::bst<sm,lg>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 2::ref [x]
                                EXISTS(l,s: x'::bst<s,l>@M[Orig][LHSCase]&
                                l<=lg & B(s,sm)&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[sm; 
                  lg](ex)x::bst<sm,lg>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 2::ref [x]
                              EXISTS(l_1004,
                              s_1005: x'::bst<s_1005,l_1004>@M[Orig][LHSCase]&
                              l_1004<=lg & s_1005=sm & sm<=lg&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (sm=s & s<=sm_619 & B(s_892,sm_619)) --> B(s,sm),
 (sm=sm_639 & s_947=s & B(s_947,sm_639)) --> B(s,sm),
 (sm=s) --> B(s,sm)]
!!! NEW ASSUME:[ RELASS [B]: ( B(s_892,sm_619)) -->  sm_619<=s_892]
!!! NEW RANK:[]
Procedure delete$node2~int SUCCESS

Termination checking result:

Stop Omega... 351 invocations 
0 false contexts at: ()

Total verification time: 0.81 second(s)
	Time spent in main process: 0.15 second(s)
	Time spent in child processes: 0.66 second(s)

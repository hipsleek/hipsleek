
Processing file "bst-insert.ss"
Parsing bst-insert.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure insert$node2~int... 
!!! REL :  C(mi,sm,ma,lg,a,res)
!!! POST:  lg>=sm & ma>=(1+lg) & res!=null & sm=mi & ma=a | a>=(1+sm) & ma>=a & 
res!=null & ma=lg & sm=mi | sm>=a & ma>=sm & res!=null & ma=lg & a=mi
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [C]
              EBase exists (Expl)(Impl)[sm; 
                    lg](ex)x::bst<sm,lg>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::
                                EXISTS(mi,
                                ma: res::bst<mi,ma>@M[Orig][LHSCase]&
                                C(mi,sm,ma,lg,a,res)&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[sm; 
                  lg](ex)x::bst<sm,lg>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 1::
                              EXISTS(mi_833,
                              ma_834: res::bst<mi_833,ma_834>@M[Orig][LHSCase]&
                              (lg>=sm & ma_834>=(1+lg) & res!=null & 
                              sm=mi_833 & ma_834=a | a>=(1+sm) & ma_834>=a & 
                              res!=null & ma_834=lg & sm=mi_833 | sm>=a & 
                              ma_834>=sm & res!=null & ma_834=lg & 
                              a=mi_833) & sm<=lg&{FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (a=mi & ma=lg & mi<=sm & sm<=lg & res!=null | mi=sm & ma=a & sm<=lg & 
  lg<a & res!=null | mi=sm & ma=lg & sm<a & a<=lg & 
  res!=null) --> C(mi,sm,ma,lg,a,res),
 (sm_621=sm & ma=lg & mi=mi_649 & sm<=lg_622 & lg_622<=lg & mi_649<=ma_650 & 
  a<=lg & res!=null & 
  C(mi_649,sm_621,ma_650,lg_622,a,v_node2_43_716)) --> C(mi,sm,ma,lg,a,res),
 (lg_657=lg & mi=sm & ma=ma_685 & sm<=sm_656 & sm_656<=lg & sm<a & 
  mi_684<=ma_685 & res!=null & 
  C(mi_684,sm_656,ma_685,lg_657,a,v_node2_48_775)) --> C(mi,sm,ma,lg,a,res)]
!!! NEW ASSUME:[ RELASS [C]: ( C(mi_649,sm_621,ma_650,lg_622,a,v_node2_43_716)) -->  lg_622<sm_621 | sm_621<=lg_622 & ma_650<=a | a<ma_650 & ma_650<mi_649 & 
sm_621<=lg_622 | (a+1)<=ma_650 & mi_649<=ma_650 & ma_650<=lg_622 & 
sm_621<=lg_622,
 RELASS [C]: ( C(mi_684,sm_656,ma_685,lg_657,a,v_node2_48_775)) -->  a<=(mi_684+1) | sm_656<=mi_684 & mi_684<=(a-2) | ma_685<mi_684 & mi_684<=(a-
2) & mi_684<=(sm_656-1) | mi_684<=(a-2) & mi_684<=(sm_656-1) & 
mi_684<=ma_685 & lg_657<sm_656]
!!! NEW RANK:[]
Procedure insert$node2~int SUCCESS

Termination checking result:

Stop Omega... 198 invocations 
0 false contexts at: ()

Total verification time: 1.28 second(s)
	Time spent in main process: 0.08 second(s)
	Time spent in child processes: 1.2 second(s)

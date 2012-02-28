
Processing file "bst-insert-a.ss"
Parsing bst-insert-a.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure insert$node2~int... 
!!! REL :  C(mi,sm,ma,lg,a)
!!! POST:  lg>=sm & ma>=(1+lg) & sm=mi & ma=a | a>=(1+sm) & ma>=a & ma=lg & sm=mi | 
sm>=a & ma>=sm & ma=lg & a=mi
!!! PRE :  sm<=lg & lg<a | sm<a & a<=lg | a<=sm & sm<=lg
!!! OLD SPECS: ((None,[]),EInfer [C]
              EBase exists (Expl)(Impl)[sm; 
                    lg](ex)x::bst<sm,lg>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::
                                EXISTS(mi,
                                ma: res::bst<mi,ma>@M[Orig][LHSCase]&
                                res!=null & C(mi,sm,ma,lg,a)&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[sm; 
                  lg](ex)x::bst<sm,lg>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&sm<=lg & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 1::
                              EXISTS(mi_801,
                              ma_802: res::bst<mi_801,ma_802>@M[Orig][LHSCase]&
                              res!=null & (lg>=sm & ma_802>=(1+lg) & 
                              sm=mi_801 & ma_802=a | a>=(1+sm) & ma_802>=a & 
                              ma_802=lg & sm=mi_801 | sm>=a & ma_802>=sm & 
                              ma_802=lg & a=mi_801) & sm<=lg&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (a=mi & ma=lg & mi<=sm & sm<=lg | mi=sm & ma=a & sm<=lg & lg<a | mi=sm & 
  ma=lg & sm<a & a<=lg) --> C(mi,sm,ma,lg,a),
 (C(mi_649,sm_621,ma_650,lg_622,a) & ma=lg & mi=mi_649 & sm_621=sm & 
  mi_649<=ma_650 & sm<=lg_622 & exists(v_606:exists(qs_605:a<=v_606 & 
  qs_605<=lg & lg_622<=v_606 & v_606<=qs_605))) --> C(mi,sm,ma,lg,a),
 (C(mi_684,sm_656,ma_685,lg_657,a) & ma=ma_685 & mi=sm & lg_657=lg & 
  mi_684<=ma_685 & sm_656<=lg & exists(v_606:exists(pl_604:sm<=pl_604 & (1+
  v_606)<=a & pl_604<=v_606 & v_606<=sm_656))) --> C(mi,sm,ma,lg,a)]
!!! NEW ASSUME:[ RELASS [C]: ( C(mi_649,sm_621,ma_650,lg_622,a)) -->  lg_622<sm_621 | sm_621<=lg_622 & ma_650<=lg_622 | sm_621<=lg_622 & 
lg_622<ma_650 & ma_650<mi_649 | sm_621<=lg_622 & lg_622<ma_650 & ma_650<=a & 
mi_649<=ma_650,
 RELASS [C]: ( C(mi_684,sm_656,ma_685,lg_657,a)) -->  sm_656<=mi_684 | ma_685<mi_684 & mi_684<sm_656 | mi_684<=(sm_656-1) & 
mi_684<=ma_685 & lg_657<sm_656 | (a-1)<=mi_684 & mi_684<sm_656 & 
sm_656<=lg_657 & mi_684<=ma_685]
!!! NEW RANK:[]
Procedure insert$node2~int SUCCESS

Termination checking result:

Stop Omega... 187 invocations 
0 false contexts at: ()

Total verification time: 1.04 second(s)
	Time spent in main process: 0.39 second(s)
	Time spent in child processes: 0.65 second(s)

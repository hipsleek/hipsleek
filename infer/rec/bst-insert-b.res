
Processing file "bst-insert-b.ss"
Parsing bst-insert-b.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure insert$node2~int... 
!!! REL :  A(mi,sm,a)
!!! POST:  a>=mi & sm>=mi
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [A]
              EBase exists (Expl)(Impl)[sm; 
                    lg](ex)x::bst<sm,lg>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::
                                EXISTS(mi,
                                ma: res::bst<mi,ma>@M[Orig][LHSCase]&
                                res!=null & A(mi,sm,a) & ma=max(lg,a)&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[sm; 
                  lg](ex)x::bst<sm,lg>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 1::
                              EXISTS(mi_802,
                              ma_803: res::bst<mi_802,ma_803>@M[Orig][LHSCase]&
                              res!=null & ma_803=max(lg,a) & a>=mi_802 & 
                              sm>=mi_802 & sm<=lg&{FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(lg:mi=a & a<=sm & sm<=lg | sm=mi & mi<=lg & (1+lg)<=a | sm=mi & (1+
  mi)<=a & a<=lg)) --> A(mi,sm,a),
 (exists(ma_651:A(mi_650,sm_622,a) & mi=mi_650 & sm_622=sm & 
  exists(lg_623:exists(qs_606:exists(ma:exists(lg_604:sm<=lg_623 & 
  exists(v_607:qs_606<=ma & lg_604=ma & (ma_651=a & mi_650<=a & (1+
  lg_623)<=a & a<=v_607 | lg_623=ma_651 & a<=ma_651 & mi_650<=ma_651 & 
  ma_651<=v_607) & v_607<=qs_606))))))) --> A(mi,sm,a),
 (exists(ma:exists(ma_686:A(mi_685,sm_657,a) & mi=sm & 
  exists(lg_604:sm_657<=lg_604 & exists(v_607:exists(pl_605:sm<=pl_605 & 
  pl_605<=v_607 & (ma_686=a & ma=a & mi_685<=a & (1+lg_604)<=a | ma=ma_686 & 
  lg_604=ma_686 & (1+v_607)<=a & a<=ma_686 & mi_685<=ma_686) & 
  v_607<=sm_657)))))) --> A(mi,sm,a)]
!!! NEW ASSUME:[ RELASS [A]: ( A(mi_685,sm_657,a)) -->  a<=(mi_685+1) | sm_657<=mi_685 & mi_685<=(a-2)]
!!! NEW RANK:[]
Procedure insert$node2~int SUCCESS

Termination checking result:

Stop Omega... 184 invocations 
0 false contexts at: ()

Total verification time: 1.1 second(s)
	Time spent in main process: 0.43 second(s)
	Time spent in child processes: 0.67 second(s)

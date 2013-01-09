Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure insert$node2~int... 
!!! REL :  C(mi,sm,ma,lg,a)
!!! POST:  (sm>=a & lg>=sm & a=mi & lg=ma) | (a>=(1+mi) & lg>=a & mi=sm & lg=ma) | 
(lg>=mi & a>=(1+lg) & mi=sm & a=ma)
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [C]
              EBase exists (Expl)(Impl)[sm; 
                    lg](ex)x::bst<sm,lg>@M[Orig][LHSCase]&true&
                    {FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 69::
                                EXISTS(mi,
                                ma: res::bst<mi,ma>@M[Orig][LHSCase]&
                                C(mi,sm,ma,lg,a) & res!=null&
                                {FLOW,(22,23)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[sm; 
                  lg](ex)x::bst<sm,lg>@M[Orig][LHSCase]&true&
                  {FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 69::
                              EXISTS(mi,ma: res::bst<mi,ma>@M[Orig][LHSCase]&
                              res!=null & ((sm>=a & lg>=sm & a=mi & lg=ma) | 
                              (a>=(1+mi) & lg>=a & mi=sm & lg=ma) | 
                              (lg>=mi & a>=(1+lg) & mi=sm & a=ma))&
                              {FLOW,(22,23)=__norm})[])
!!! NEW RELS:[ ((mi=sm & a=ma & mi<=lg & lg<a) | (mi=sm & lg=ma & (mi+1)<=a & a<=lg) | 
  (a=mi & lg=ma & a<=sm & sm<=lg)) --> C(mi,sm,ma,lg,a),
 (((mi=mi_662 & lg=ma & sm=sm_647 & mi_662<=ma_663 & ma_663<=lg_648 & 
  lg_648<=lg & sm<=lg_648 & a<=lg) | (mi=mi_662 & lg=ma & sm=sm_647 & 
  sm<=lg_648 & lg_648<ma_663 & ma_663<=a & a<=lg & mi_662<=ma_663)) & 
  C(mi_662,sm_647,ma_663,lg_648,a)) --> C(mi,sm,ma,lg,a),
 (((lg=lg_670 & ma=ma_685 & mi=sm & sm<=sm_669 & sm_669<=mi_684 & 
  mi_684<=ma_685 & sm<a & sm_669<=lg) | (lg=lg_670 & ma=ma_685 & mi=sm & (a-
  1)<=mi_684 & mi_684<sm_669 & sm_669<=lg & sm<a & mi_684<=ma_685)) & 
  C(mi_684,sm_669,ma_685,lg_670,a)) --> C(mi,sm,ma,lg,a)]
!!! NEW ASSUME:[ RELASS [C]: ( C(mi_662,sm_647,ma_663,lg_648,a)) -->  ((lg_648<ma_663 & ma_663<=a & mi_662<=ma_663) | ma_663<=lg_648) & 
sm_647<=lg_648,
 RELASS [C]: ( C(mi_684,sm_669,ma_685,lg_670,a)) -->  ((mi_684<sm_669 & (a-1)<=mi_684 & mi_684<=ma_685) | sm_669<=mi_684) & 
sm_669<=lg_670]
Procedure insert$node2~int SUCCESS

Termination checking result:

Stop Omega... 181 invocations 
0 false contexts at: ()

Total verification time: 0.9 second(s)
	Time spent in main process: 0.54 second(s)
	Time spent in child processes: 0.36 second(s)


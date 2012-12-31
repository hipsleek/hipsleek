Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure insert$node2~int... 
!!! REL :  C(mi,sm,ma,lg,a)
!!! POST:  lg>=sm & ma>=(1+lg) & sm=mi & ma=a | a>=(1+sm) & ma>=a & ma=lg & sm=mi | 
sm>=a & ma>=sm & ma=lg & a=mi
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
                              res!=null & (lg>=sm & ma>=(1+lg) & sm=mi & 
                              ma=a | a>=(1+sm) & ma>=a & ma=lg & sm=mi | 
                              sm>=a & ma>=sm & ma=lg & a=mi)&
                              {FLOW,(22,23)=__norm})[])
!!! NEW RELS:[ (a=mi & ma=lg & mi<=sm & sm<=lg | mi=sm & ma=a & sm<=lg & lg<a | mi=sm & 
  ma=lg & sm<a & a<=lg) --> C(mi,sm,ma,lg,a),
 (lg=ma & sm=sm_651 & a=a' & mi_668=mi & sm_651<=lg_652 & lg_652<=ma & 
  mi<=ma_669 & a'<=ma & 
  C(mi_668,sm_651,ma_669,lg_652,a')) --> C(mi,sm,ma,lg,a),
 (sm=mi & lg=lg_676 & a=a' & ma_693=ma & mi<=sm_675 & sm_675<=lg_676 & 
  mi<a' & mi_692<=ma & 
  C(mi_692,sm_675,ma_693,lg_676,a')) --> C(mi,sm,ma,lg,a)]
!!! NEW ASSUME:[ RELASS [C]: ( C(mi_668,sm_651,ma_669,lg_652,a')) -->  lg_652<sm_651 | sm_651<=lg_652 & ma_669<mi_668 | mi_668<=ma_669 & 
ma_669<=a' & sm_651<=lg_652 | mi_668<=ma_669 & (a'+1)<=ma_669 & 
ma_669<=lg_652 & sm_651<=lg_652,
 RELASS [C]: ( C(mi_692,sm_675,ma_693,lg_676,a')) -->  ma_693<mi_692 | lg_676<sm_675 & mi_692<=ma_693 | sm_675<=mi_692 & 
mi_692<=ma_693 & sm_675<=lg_676 | (a'-1)<=mi_692 & mi_692<sm_675 & 
sm_675<=lg_676 & mi_692<=ma_693]
!!! NEW RANK:[]
Procedure insert$node2~int SUCCESS

Termination checking result:

Stop Omega... 146 invocations 
0 false contexts at: ()

Total verification time: 1.51 second(s)
	Time spent in main process: 0.46 second(s)
	Time spent in child processes: 1.05 second(s)

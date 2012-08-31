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
                    {FLOW,(20,21)=__norm}[]
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                              EAssume 69::
                                EXISTS(mi,
                                ma: res::bst<mi,ma>@M[Orig][LHSCase]&
                                res!=null & C(mi,sm,ma,lg,a)&
                                {FLOW,(20,21)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[sm; 
                  lg](ex)x::bst<sm,lg>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}[]
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                            EAssume 69::
                              EXISTS(mi,ma: res::bst<mi,ma>@M[Orig][LHSCase]&
                              res!=null & (lg>=sm & ma>=(1+lg) & sm=mi & 
                              ma=a | a>=(1+sm) & ma>=a & ma=lg & sm=mi | 
                              sm>=a & ma>=sm & ma=lg & a=mi)&
                              {FLOW,(20,21)=__norm})[])
!!! NEW RELS:[ (a=mi & ma=lg & mi<=sm & sm<=lg | mi=sm & ma=a & sm<=lg & lg<a | mi=sm & 
  ma=lg & sm<a & a<=lg) --> C(mi,sm,ma,lg,a),
 (lg=ma & sm=sm_634 & a=a' & mi_651=mi & sm_634<=lg_635 & lg_635<=ma & 
  mi<=ma_652 & a'<=ma & 
  C(mi_651,sm_634,ma_652,lg_635,a')) --> C(mi,sm,ma,lg,a),
 (sm=mi & lg=lg_659 & a=a' & ma_676=ma & mi<=sm_658 & sm_658<=lg_659 & 
  mi<a' & mi_675<=ma & 
  C(mi_675,sm_658,ma_676,lg_659,a')) --> C(mi,sm,ma,lg,a)]
!!! NEW ASSUME:[ RELASS [C]: ( C(mi_651,sm_634,ma_652,lg_635,a')) -->  lg_635<sm_634 | sm_634<=lg_635 & ma_652<mi_651 | mi_651<=ma_652 & 
ma_652<=a' & sm_634<=lg_635 | mi_651<=ma_652 & (a'+1)<=ma_652 & 
ma_652<=lg_635 & sm_634<=lg_635,
 RELASS [C]: ( C(mi_675,sm_658,ma_676,lg_659,a')) -->  ma_676<mi_675 | lg_659<sm_658 & mi_675<=ma_676 | sm_658<=mi_675 & 
mi_675<=ma_676 & sm_658<=lg_659 | (a'-1)<=mi_675 & mi_675<sm_658 & 
sm_658<=lg_659 & mi_675<=ma_676]
!!! NEW RANK:[]
Procedure insert$node2~int SUCCESS

Termination checking result:

Stop Omega... 152 invocations 
0 false contexts at: ()

Total verification time: 1.46 second(s)
	Time spent in main process: 0.43 second(s)
	Time spent in child processes: 1.03 second(s)

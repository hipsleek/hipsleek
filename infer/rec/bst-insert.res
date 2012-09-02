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
                    {FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 69::
                                EXISTS(mi,
                                ma: res::bst<mi,ma>@M[Orig][LHSCase]&
                                C(mi,sm,ma,lg,a,res)&{FLOW,(22,23)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[sm; 
                  lg](ex)x::bst<sm,lg>@M[Orig][LHSCase]&true&
                  {FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 69::
                              EXISTS(mi,ma: res::bst<mi,ma>@M[Orig][LHSCase]&
                              lg>=sm & ma>=(1+lg) & res!=null & sm=mi & 
                              ma=a | a>=(1+sm) & ma>=a & res!=null & ma=lg & 
                              sm=mi | sm>=a & ma>=sm & res!=null & ma=lg & 
                              a=mi&{FLOW,(22,23)=__norm})[])
!!! NEW RELS:[ (a=mi & ma=lg & mi<=sm & sm<=lg & res!=null | mi=sm & ma=a & sm<=lg & 
  lg<a & res!=null | mi=sm & ma=lg & sm<a & a<=lg & 
  res!=null) --> C(mi,sm,ma,lg,a,res),
 (sm_651=sm & mi=mi_668 & a'=a & ma=lg & sm<=lg_652 & lg_652<=lg & a<=lg & 
  mi_668<=ma_669 & res!=null & 
  C(mi_668,sm_651,ma_669,lg_652,a',v_node2_43_724)) --> C(mi,sm,ma,lg,a,res),
 (lg_676=lg & mi=sm & a'=a & ma=ma_693 & sm<=sm_675 & sm_675<=lg & sm<a & 
  mi_692<=ma_693 & res!=null & 
  C(mi_692,sm_675,ma_693,lg_676,a',v_node2_48_753)) --> C(mi,sm,ma,lg,a,res)]
!!! NEW ASSUME:[ RELASS [C]: ( C(mi_668,sm_651,ma_669,lg_652,a',v_node2_43_724)) -->  lg_652<sm_651 | sm_651<=lg_652 & ma_669<mi_668 | mi_668<=ma_669 & 
ma_669<=lg_652 & sm_651<=lg_652 | sm_651<=lg_652 & lg_652<ma_669 & 
ma_669<=a' & mi_668<=ma_669,
 RELASS [C]: ( C(mi_692,sm_675,ma_693,lg_676,a',v_node2_48_753)) -->  lg_676<sm_675 & v_node2_48_753=null | sm_675<=lg_676 & sm_675<=mi_692 & 
v_node2_48_753=null | (a'-1)<=mi_692 & mi_692<sm_675 & sm_675<=lg_676 & 
v_node2_48_753=null | ma_693<mi_692 & mi_692<sm_675 & sm_675<=lg_676 & 
v_node2_48_753=null & mi_692<=(a'-2) | lg_676<sm_675 & 
v_node2_48_753!=null | a'<=(mi_692+1) & sm_675<=lg_676 & 
v_node2_48_753!=null | sm_675<=mi_692 & mi_692<=(a'-2) & sm_675<=lg_676 & 
v_node2_48_753!=null | ma_693<mi_692 & mi_692<sm_675 & sm_675<=lg_676 & 
mi_692<=(a'-2) & v_node2_48_753!=null]
!!! NEW RANK:[]
Procedure insert$node2~int SUCCESS

Termination checking result:

Stop Omega... 152 invocations 
0 false contexts at: ()

Total verification time: 3.52 second(s)
	Time spent in main process: 0.46 second(s)
	Time spent in child processes: 3.06 second(s)

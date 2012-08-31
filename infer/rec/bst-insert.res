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
                    {FLOW,(20,21)=__norm}[]
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                              EAssume 69::
                                EXISTS(mi,
                                ma: res::bst<mi,ma>@M[Orig][LHSCase]&
                                C(mi,sm,ma,lg,a,res)&{FLOW,(20,21)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[sm; 
                  lg](ex)x::bst<sm,lg>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}[]
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                            EAssume 69::
                              EXISTS(mi,ma: res::bst<mi,ma>@M[Orig][LHSCase]&
                              lg>=sm & ma>=(1+lg) & res!=null & sm=mi & 
                              ma=a | a>=(1+sm) & ma>=a & res!=null & ma=lg & 
                              sm=mi | sm>=a & ma>=sm & res!=null & ma=lg & 
                              a=mi&{FLOW,(20,21)=__norm})[])
!!! NEW RELS:[ (a=mi & ma=lg & mi<=sm & sm<=lg & res!=null | mi=sm & ma=a & sm<=lg & 
  lg<a & res!=null | mi=sm & ma=lg & sm<a & a<=lg & 
  res!=null) --> C(mi,sm,ma,lg,a,res),
 (sm_634=sm & mi=mi_651 & a'=a & ma=lg & sm<=lg_635 & lg_635<=lg & a<=lg & 
  mi_651<=ma_652 & res!=null & 
  C(mi_651,sm_634,ma_652,lg_635,a',v_node2_43_707)) --> C(mi,sm,ma,lg,a,res),
 (lg_659=lg & mi=sm & a'=a & ma=ma_676 & sm<=sm_658 & sm_658<=lg & sm<a & 
  mi_675<=ma_676 & res!=null & 
  C(mi_675,sm_658,ma_676,lg_659,a',v_node2_48_736)) --> C(mi,sm,ma,lg,a,res)]
!!! NEW ASSUME:[ RELASS [C]: ( C(mi_651,sm_634,ma_652,lg_635,a',v_node2_43_707)) -->  lg_635<sm_634 | sm_634<=lg_635 & ma_652<mi_651 | mi_651<=ma_652 & 
ma_652<=lg_635 & sm_634<=lg_635 | sm_634<=lg_635 & lg_635<ma_652 & 
ma_652<=a' & mi_651<=ma_652,
 RELASS [C]: ( C(mi_675,sm_658,ma_676,lg_659,a',v_node2_48_736)) -->  lg_659<sm_658 & v_node2_48_736=null | sm_658<=lg_659 & sm_658<=mi_675 & 
v_node2_48_736=null | (a'-1)<=mi_675 & mi_675<sm_658 & sm_658<=lg_659 & 
v_node2_48_736=null | ma_676<mi_675 & mi_675<sm_658 & sm_658<=lg_659 & 
v_node2_48_736=null & mi_675<=(a'-2) | lg_659<sm_658 & 
v_node2_48_736!=null | a'<=(mi_675+1) & sm_658<=lg_659 & 
v_node2_48_736!=null | sm_658<=mi_675 & mi_675<=(a'-2) & sm_658<=lg_659 & 
v_node2_48_736!=null | ma_676<mi_675 & mi_675<sm_658 & sm_658<=lg_659 & 
mi_675<=(a'-2) & v_node2_48_736!=null]
!!! NEW RANK:[]
Procedure insert$node2~int SUCCESS

Termination checking result:

Stop Omega... 156 invocations 
0 false contexts at: ()

Total verification time: 2.49 second(s)
	Time spent in main process: 0.43 second(s)
	Time spent in child processes: 2.06 second(s)

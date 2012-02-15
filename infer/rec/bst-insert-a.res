
Processing file "bst-insert-a.ss"
Parsing bst-insert-a.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure insert$node2~int... 
INF-POST-FLAG: false
REL :  C(mi,sm,ma,lg,a)
POST:  ma>=lg & sm>=mi & (lg+a)>=(ma+mi) & (ma+mi)>=(sm+a)
PRE :  sm<=lg
OLD SPECS:  EInfer [C]
   EBase exists (Expl)(Impl)[sm; lg](ex)x::bst<sm,lg>@M[Orig][LHSCase]&true&
         {FLOW,(20,21)=__norm}
           EBase true&MayLoop&{FLOW,(1,23)=__flow}
                   EAssume 1::
                     EXISTS(mi,ma: res::bst<mi,ma>@M[Orig][LHSCase]&
                     res!=null & C(mi,sm,ma,lg,a)&{FLOW,(20,21)=__norm})
NEW SPECS:  EBase exists (Expl)(Impl)[sm; lg](ex)x::bst<sm,lg>@M[Orig][LHSCase]&true&
       {FLOW,(20,21)=__norm}
         EBase true&sm<=lg & MayLoop&{FLOW,(1,23)=__flow}
                 EAssume 1::
                   res::bst<mi,ma>@M[Orig][LHSCase]&res!=null & 
                   C(mi,sm,ma,lg,a) & sm<=lg&{FLOW,(20,21)=__norm}
NEW RELS: [ (a=mi & ma=lg & mi<=sm & sm<=lg | mi=sm & ma=a & sm<=lg & lg<a | mi=sm & 
  ma=lg & sm<a & a<=lg) --> C(mi,sm,ma,lg,a), ((mi_649=mi & lg=ma & sm=sm_621 & mi<=ma_650 & ma_650<=a & a<=ma & 
  sm_621<=lg_622 & lg_622<=ma | mi_649=mi & lg=ma & sm=sm_621 & mi<=ma_650 & 
  (a+1)<=ma_650 & ma_650<=lg_622 & lg_622<=ma & sm_621<=lg_622) & 
  C(mi_649,sm_621,ma_650,lg_622,a)) --> C(mi,sm,ma,lg,a), ((sm=mi & ma_685=ma & lg=lg_657 & mi<a & a<=(mi_684+1) & mi<=sm_656 & 
  sm_656<=lg_657 & mi_684<=ma | sm=mi & ma_685=ma & lg=lg_657 & mi<=sm_656 & 
  sm_656<=mi_684 & mi_684<=ma & mi_684<=(a-2) & sm_656<=lg_657) & 
  C(mi_684,sm_656,ma_685,lg_657,a)) --> C(mi,sm,ma,lg,a)]

Procedure insert$node2~int SUCCESS

Termination checking result:

Stop Omega... 348 invocations 
0 false contexts at: ()

Total verification time: 1.48 second(s)
	Time spent in main process: 0.65 second(s)
	Time spent in child processes: 0.83 second(s)

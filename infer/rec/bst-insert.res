
Processing file "bst-insert.ss"
Parsing bst-insert.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure insert$node2~int... 
INF-POST-FLAG: false
REL :  C(mi,sm,ma,lg,a,res)
POST:  ma>=lg & sm>=mi & (lg+a)>=(ma+mi) & (ma+mi)>=(sm+a) & res!=null
PRE :  sm<=lg
OLD SPECS:  EInfer [C]
   EBase exists (Expl)(Impl)[sm; lg](ex)x::bst<sm,lg>@M[Orig][LHSCase]&true&
         {FLOW,(20,21)=__norm}
           EBase true&MayLoop&{FLOW,(1,23)=__flow}
                   EAssume 1::
                     EXISTS(mi,ma: res::bst<mi,ma>@M[Orig][LHSCase]&
                     C(mi,sm,ma,lg,a,res)&{FLOW,(20,21)=__norm})
NEW SPECS:  EBase exists (Expl)(Impl)[sm; lg](ex)x::bst<sm,lg>@M[Orig][LHSCase]&true&
       {FLOW,(20,21)=__norm}
         EBase true&sm<=lg & MayLoop&{FLOW,(1,23)=__flow}
                 EAssume 1::
                   res::bst<mi,ma>@M[Orig][LHSCase]&C(mi,sm,ma,lg,a,res) & 
                   sm<=lg&{FLOW,(20,21)=__norm}
NEW RELS: [ (a=mi & ma=lg & mi<=sm & sm<=lg & res!=null | mi=sm & ma=a & sm<=lg & 
  lg<a & res!=null | mi=sm & ma=lg & sm<a & a<=lg & 
  res!=null) --> C(mi,sm,ma,lg,a,res), (sm_621=sm & ma=lg & sm<=lg_622 & lg_622<=lg & mi_649<=ma_650 & 
  v_node2_43_716=null & mi<=lg & a<=lg & res!=null & 
  C(mi_649,sm_621,ma_650,lg_622,a,v_node2_43_716)) --> C(mi,sm,ma,lg,a,res), ((lg=lg_657 & sm=mi & ma_685=ma & mi<=sm_656 & sm_656<=mi_684 & 
  mi_684<=ma & mi<a & sm_656<=lg_657 & res!=null | lg=lg_657 & sm=mi & 
  ma_685=ma & (a-1)<=mi_684 & mi_684<sm_656 & sm_656<=lg_657 & mi<a & 
  mi_684<=ma & res!=null) & 
  C(mi_684,sm_656,ma_685,lg_657,a,v_node2_48_784)) --> C(mi,sm,ma,lg,a,res)]

Procedure insert$node2~int SUCCESS

Termination checking result:

Stop Omega... 375 invocations 
0 false contexts at: ()

Total verification time: 1.85 second(s)
	Time spent in main process: 0.72 second(s)
	Time spent in child processes: 1.13 second(s)

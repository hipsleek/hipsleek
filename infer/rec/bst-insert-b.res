
Processing file "bst-insert-b.ss"
Parsing bst-insert-b.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure insert$node2~int... 
INF-POST-FLAG: false
REL :  A(mi,sm,a)
POST:  sm>=mi & mi=a | a>=(1+mi) & mi=sm
PRE :  a<=sm | sm<a
OLD SPECS:  EInfer [A]
   EBase exists (Expl)(Impl)[sm; lg](ex)x::bst<sm,lg>@M[Orig][LHSCase] &
         true & {FLOW,(20,21)=__norm}
           EBase true & MayLoop & {FLOW,(1,23)=__flow}
                   EAssume 1::
                     EXISTS(mi,ma: res::bst<mi,ma>@M[Orig][LHSCase] &
                     res!=null & A(mi,sm,a) & ma=max(lg,a) &
                     {FLOW,(20,21)=__norm})
NEW SPECS:  EBase exists (Expl)(Impl)[sm; lg](ex)x::bst<sm,lg>@M[Orig][LHSCase] & true &
       {FLOW,(20,21)=__norm}
         EBase true & MayLoop & {FLOW,(1,23)=__flow}
                 EAssume 1::
                   res::bst<mi,ma>@M[Orig][LHSCase] & res!=null & 
                   A(mi,sm,a) & ma=max(lg,a) & sm<=lg & {FLOW,(20,21)=__norm}
NEW RELS: [ ( a=mi & mi<=sm | mi=sm & sm<a) -->  A(mi,sm,a), ( sm_622=sm & mi=mi_650 & A(mi_650,sm_622,a)) -->  A(mi,sm,a), ( (sm=mi & mi<a & a<=(mi_685+1) & mi<=sm_657 | sm=mi & mi<=sm_657 & 
sm_657<=mi_685 & mi_685<=a & sm_657<a) & A(mi_685,sm_657,a)) -->  A(mi,sm,a)]

Procedure insert$node2~int SUCCESS

Termination checking result:

Stop Omega... 244 invocations 
0 false contexts at: ()

Total verification time: 1.42 second(s)
	Time spent in main process: 0.44 second(s)
	Time spent in child processes: 0.98 second(s)

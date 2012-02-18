
Processing file "bsort-4.ss"
Parsing bsort-4.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure bubble$node... 
INF-POST-FLAG: false
REL :  A(res)
POST:  !(res)
PRE :  true
OLD SPECS:  EInfer [A]
   EBase exists (Expl)(Impl)[n](ex)xs::ll<n>@M[Orig][LHSCase]&xs!=null&
         {FLOW,(20,21)=__norm}
           EBase true&MayLoop&{FLOW,(1,23)=__flow}
                   EAssume 1::
                     
                     EXISTS(n_38,s,l: xs::sll<n_38,s,l>@M[Orig][LHSCase]&
                     A(res) & n_38=n&{FLOW,(20,21)=__norm})
                     or EXISTS(n_39: xs::ll<n_39>@M[Orig][LHSCase]&res & 
                        n_39=n&{FLOW,(20,21)=__norm})
                     
NEW SPECS:  EBase exists (Expl)(Impl)[n](ex)xs::ll<n>@M[Orig][LHSCase]&xs!=null&
       {FLOW,(20,21)=__norm}
         EBase true&MayLoop&{FLOW,(1,23)=__flow}
                 EAssume 1::
                   
                   xs::ll<n_39>@M[Orig][LHSCase]&res & n_39=n & 0<=n&
                   {FLOW,(20,21)=__norm}
                   or xs::sll<n_38,s,l>@M[Orig][LHSCase]&A(res) & n_38=n & 
                      0<=n&{FLOW,(20,21)=__norm}
                   
NEW RELS: [ (tmp_42' & 1<=res & A(tmp_42')) --> A(res), (1<=res & tmp_42' & A(tmp_42')) --> A(res), (res<=0) --> A(res), (!(tmp_42') & res<=0 & A(tmp_42')) --> A(res), (res<=0 & !(tmp_42') & A(tmp_42')) --> A(res)]

Procedure bubble$node SUCCESS

Termination checking result:

Stop Omega... 677 invocations 
0 false contexts at: ()

Total verification time: 2.27 second(s)
	Time spent in main process: 1.48 second(s)
	Time spent in child processes: 0.79 second(s)

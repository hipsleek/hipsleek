
Processing file "bst-remove-min.ss"
Parsing bst-remove-min.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure remove_min$node2... 
Inferred Heap:[]
Inferred Pure:[ x!=null, x!=null]

INF-POST-FLAG: false
REL :  A(s,res,s1)
POST:  res>=s & s1>=res
PRE :  true
OLD SPECS:  EInfer [x,A]
   EBase exists (Expl)(Impl)[s; b](ex)x::bst<s,b>@M[Orig][LHSCase]&true&
         {FLOW,(20,21)=__norm}
           EBase true&MayLoop&{FLOW,(1,23)=__flow}
                   EAssume 1::ref [x]
                     EXISTS(b_30,s1: x'::bst<s1,b_30>@M[Orig][LHSCase]&
                     A(s,res,s1) & b_30=b&{FLOW,(20,21)=__norm})
NEW SPECS:  EBase exists (Expl)(Impl)[s; b](ex)x::bst<s,b>@M[Orig][LHSCase]&true&
       {FLOW,(20,21)=__norm}
         EBase true&x!=null & MayLoop&{FLOW,(1,23)=__flow}
                 EAssume 1::ref [x]
                   x'::bst<s1,b_30>@M[Orig][LHSCase]&A(s,res,s1) & b_30=b & 
                   s<=b&{FLOW,(20,21)=__norm}
NEW RELS: [ (s<=res & res<=s1) --> A(s,res,s1), (s_600=s & s1=s1_628 & tmp_33'=res & 
  A(s_600,tmp_33',s1_628)) --> A(s,res,s1)]

Procedure remove_min$node2 SUCCESS

Termination checking result:

Stop Omega... 194 invocations 
0 false contexts at: ()

Total verification time: 0.74 second(s)
	Time spent in main process: 0.37 second(s)
	Time spent in child processes: 0.37 second(s)

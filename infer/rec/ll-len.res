
Processing file "ll-len.ss"
Parsing ll-len.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure length$node... 
INF-POST-FLAG: true
REL :  R(res,n)
POST:  res>=0 & res=n
PRE :  0<=n
OLD SPECS:  EInfer [R]
   EBase exists (Expl)(Impl)[n](ex)x::ll<n>@L[Orig][LHSCase]&true&
         {FLOW,(20,21)=__norm}
           EBase true&MayLoop&{FLOW,(1,23)=__flow}
                   EAssume 1::
                     true&R(res,n)&{FLOW,(20,21)=__norm}
NEW SPECS:  EBase exists (Expl)(Impl)[n](ex)x::ll<n>@L[Orig][LHSCase]&true&
       {FLOW,(20,21)=__norm}
         EBase true&0<=n & MayLoop&{FLOW,(1,23)=__flow}
                 EAssume 1::
                   true&res>=0 & res=n & 0<=n&{FLOW,(20,21)=__norm}
NEW RELS: [ (n=0 & res=0) --> R(res,n), (r_24'=res-1 & n_539=n-1 & 1<=n & R(r_24',n_539)) --> R(res,n)]

Procedure length$node SUCCESS

Termination checking result:

Stop Omega... 102 invocations 
0 false contexts at: ()

Total verification time: 0.2 second(s)
	Time spent in main process: 0.15 second(s)
	Time spent in child processes: 0.05 second(s)

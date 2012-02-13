
Processing file "cll-count2.ss"
Parsing cll-count2.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure count$node... 
INF-POST-FLAG: false
REL :  A(res,n)
POST:  res>=0 & res=n
PRE :  0<=n
OLD SPECS:  EInfer [A]
   EBase exists (Expl)(Impl)[n](ex)x::hd<n>@M[Orig][LHSCase]&true&
         {FLOW,(20,21)=__norm}
           EBase true&MayLoop&{FLOW,(1,23)=__flow}
                   EAssume 2::
                     EXISTS(n_29: x::hd<n_29>@M[Orig][LHSCase]&A(res,n) & 
                     n_29=n&{FLOW,(20,21)=__norm})
NEW SPECS:  EBase exists (Expl)(Impl)[n](ex)x::hd<n>@M[Orig][LHSCase]&true&
       {FLOW,(20,21)=__norm}
         EBase true&0<=n & MayLoop&{FLOW,(1,23)=__flow}
                 EAssume 2::
                   x::hd<n_29>@M[Orig][LHSCase]&A(res,n) & n_29=n & 0<=n&
                   {FLOW,(20,21)=__norm}
NEW RELS: [ (res=0 & n=0) --> A(res,n), (res=0 & n=0) --> A(res,n), (n=res & 1<=res) --> A(res,n), (res=0 & n=0) --> A(res,n), (n=1 & res=1) --> A(res,n), (n=1 & res=1) --> A(res,n), (n=1 & res=1) --> A(res,n), (n=1 & res=1) --> A(res,n), (n=1 & res=1) --> A(res,n), (n=1 & res=1) --> A(res,n), (n=1 & res=1) --> A(res,n), (n=1 & res=1) --> A(res,n), (n=1 & res=1) --> A(res,n), (n=1 & res=1) --> A(res,n), (n=1 & res=1) --> A(res,n), (n=1 & res=1) --> A(res,n), (n=1 & res=1) --> A(res,n), (n=1 & res=1) --> A(res,n), (n=1 & res=1) --> A(res,n), (n=1 & res=1) --> A(res,n), (n=1 & res=1) --> A(res,n), (n=1 & res=1) --> A(res,n), (n=1 & res=1) --> A(res,n), (n=1 & res=1) --> A(res,n), (n=1 & res=1) --> A(res,n), (n=1 & res=1) --> A(res,n), (n=1 & res=1) --> A(res,n), (res=0 & n=0) --> A(res,n), (n=1 & res=1) --> A(res,n)]

Procedure count$node SUCCESS

Termination checking result:

Stop Omega... 491 invocations 
0 false contexts at: ()

Total verification time: 1.6 second(s)
	Time spent in main process: 1.03 second(s)
	Time spent in child processes: 0.57 second(s)

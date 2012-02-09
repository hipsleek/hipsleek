
Processing file "cll-del.ss"
Parsing cll-del.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure delete$node... 
INF-POST-FLAG: false
REL :  A(m,n)
POST:  m>=0 & m+1=n
PRE :  1<=n
OLD SPECS:  EInfer [n,A]
   EBase exists (Expl)(Impl)[n](ex)x::hd<n>@M[Orig][LHSCase] & 0<n &
         {FLOW,(20,21)=__norm}
           EBase true & MayLoop & {FLOW,(1,23)=__flow}
                   EAssume 1::ref [x]
                     EXISTS(m: x'::hd<m>@M[Orig][LHSCase] & A(m,n) &
                     {FLOW,(20,21)=__norm})
NEW SPECS:  EBase exists (Expl)(Impl)[n](ex)x::hd<n>@M[Orig][LHSCase] & 1<=n &
       {FLOW,(20,21)=__norm}
         EBase true & 1<=n & MayLoop & {FLOW,(1,23)=__flow}
                 EAssume 1::ref [x]
                   x'::hd<m>@M[Orig][LHSCase] & A(m,n) & 0<=n &
                   {FLOW,(20,21)=__norm}
NEW RELS: [ ( m=n - 1 & 2<=n) -->  A(m,n), ( n=1 & m=0) -->  A(m,n), ( m=1 & n=2) -->  A(m,n)]

Procedure delete$node SUCCESS

Termination checking result:

Stop Omega... 129 invocations 
0 false contexts at: ()

Total verification time: 0.39 second(s)
	Time spent in main process: 0.19 second(s)
	Time spent in child processes: 0.2 second(s)

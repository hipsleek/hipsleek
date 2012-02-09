
Processing file "ll-app.ss"
Parsing ll-app.ss ...
Parsing ../../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure append$node~node... 
!!! Inferred constraints:[ n!=0, n!=0]
Inferred Heap:[]
Inferred Pure:[ n!=0, n!=0]

INF-POST-FLAG: true
REL :  A(z,m,n)
POST:  n>=1 & m>=0 & n+m=z
PRE :  1<=n & 0<=m
OLD SPECS:  EInfer [n,A]
   EBase exists (Expl)(Impl)[n; m](ex)x::ll<n>@M[Orig][LHSCase] * 
         y::ll<m>@M[Orig][LHSCase] & true & {FLOW,(20,21)=__norm}
           EBase true & MayLoop & {FLOW,(1,23)=__flow}
                   EAssume 1::
                     EXISTS(z: x::ll<z>@M[Orig][LHSCase] & A(z,m,n) &
                     {FLOW,(20,21)=__norm})
NEW SPECS:  EBase exists (Expl)(Impl)[n; m](ex)x::ll<n>@M[Orig][LHSCase] * 
       y::ll<m>@M[Orig][LHSCase] & true & {FLOW,(20,21)=__norm}
         EBase true & 1<=n & 0<=m & MayLoop & {FLOW,(1,23)=__flow}
                 EAssume 1::
                   x::ll<z>@M[Orig][LHSCase] & n>=1 & m>=0 & n+m=z & 0<=n & 
                   0<=m & {FLOW,(20,21)=__norm}
NEW RELS: [ ( n=1 & m=z - 1 & 1<=z) -->  A(z,m,n), ( z=z_578+1 & m_556=m & n_555=n - 1 & 1<=z_578 & 0<=m & 1<=n & 
A(z_578,m_556,n_555)) -->  A(z,m,n)]

Procedure append$node~node SUCCESS

Termination checking result:

Stop Omega... 126 invocations 
0 false contexts at: ()

Total verification time: 0.24 second(s)
	Time spent in main process: 0.18 second(s)
	Time spent in child processes: 0.06 second(s)

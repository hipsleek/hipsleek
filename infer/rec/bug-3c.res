
Processing file "bug-3c.ss"
Parsing bug-3c.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure append$node~node... 
Inferred Heap:[]
Inferred Pure:[ n!=0 | m!=0, n!=0 | m<=0, n!=0 | m!=0, n!=0 | m<=0]

INF-POST-FLAG: true
REL :  A(n,m,z)
POST:  n>=1 & m>=0 & n+m=z
PRE :  1<=n & 0<=m
OLD SPECS:  EInfer [n,m,A]
   EBase exists (Expl)(Impl)[n; m](ex)x::ll<n>@M[Orig][LHSCase] * 
         y::ll<m>@M[Orig][LHSCase]&0<=n & 0<=m&{FLOW,(20,21)=__norm}
           EBase true&MayLoop&{FLOW,(1,23)=__flow}
                   EAssume 1::
                     EXISTS(z: x::ll<z>@M[Orig][LHSCase]&A(n,m,z)&
                     {FLOW,(20,21)=__norm})
NEW SPECS:  EBase exists (Expl)(Impl)[n; m](ex)x::ll<n>@M[Orig][LHSCase] * 
       y::ll<m>@M[Orig][LHSCase]&0<=n & 0<=m&{FLOW,(20,21)=__norm}
         EBase true&1<=n & 0<=m & MayLoop&{FLOW,(1,23)=__flow}
                 EAssume 1::
                   x::ll<z>@M[Orig][LHSCase]&n>=1 & m>=0 & n+m=z & 0<=n & 
                   0<=m&{FLOW,(20,21)=__norm}
NEW RELS: [ (n=1 & m=z-1 & 1<=z) --> A(n,m,z), (z=z_580+1 & n_557=n-1 & m_558=m & 1<=z_580 & 1<=n & 0<=m & 
  A(n_557,m_558,z_580)) --> A(n,m,z)]

Procedure append$node~node SUCCESS

Termination checking result:

Stop Omega... 168 invocations 
0 false contexts at: ()

Total verification time: 0.37 second(s)
	Time spent in main process: 0.26 second(s)
	Time spent in child processes: 0.11 second(s)

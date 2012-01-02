
Processing file "ll-app.ss"
Parsing ll-app.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure append$node~node... 
Inferred Heap:[]
Inferred Pure:[ x!=null, x!=null, x!=null, x!=null]

FIXPOINT:  m>=0 & z>=(1+m) & z=n+m
OLD SPECS:  EInfer [x,A]
   EBase exists (Expl)(Impl)[n; m](ex)x::ll<n>@M[Orig][LHSCase] * 
         y::ll<m>@M[Orig][LHSCase] & true & {FLOW,(20,21)=__norm}
           EAssume 1::
             EXISTS(z: x::ll<z>@M[Orig][LHSCase] & A(n,m,z) &
             {FLOW,(20,21)=__norm})
NEW SPECS:  EBase exists (Expl)(Impl)[n; m](ex)x::ll<n>@M[Orig][LHSCase] * 
       y::ll<m>@M[Orig][LHSCase] & x!=null & {FLOW,(20,21)=__norm}
         EAssume 1::
           x::ll<z>@M[Orig][LHSCase] & m=z - n & 1<=n & n<=z & 0<=n & 0<=m &
           {FLOW,(20,21)=__norm}
NEW RELS: [ ( (m=0 | 1<=m) & 1+m=z & n=1) -->  A(n,m,z), ( 0<=m_556 & 0<=n_555 & 1<=z_578 & m_556=m & A(n_555,m_556,z_578) & 1+
z_578=z & 1+n_555=n) -->  A(n,m,z)]

Procedure append$node~node SUCCESS
Stop Omega... 85 invocations 
0 false contexts at: ()

Total verification time: 0.4 second(s)
	Time spent in main process: 0.34 second(s)
	Time spent in child processes: 0.06 second(s)

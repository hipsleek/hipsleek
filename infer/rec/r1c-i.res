
Processing file "r1c-i.ss"
Parsing r1c-i.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure append$node~node... 
Inferred Heap:[]
Inferred Pure:[ x!=null, x!=null, x!=null, x!=null]
OLD SPECS:  EInfer [x,A]
   EBase exists (Expl)(Impl)[n; m](ex)x::ll<n>@M[Orig][LHSCase] * 
         y::ll<m>@M[Orig][LHSCase] & true & {FLOW,(20,21)=__norm}
           EAssume 1::
             EXISTS(z: x::ll<z>@M[Orig][LHSCase] & A(n,m,z) &
             {FLOW,(20,21)=__norm})
NEW SPECS:  EBase exists (Expl)(Impl)[n; m](ex)x::ll<n>@M[Orig][LHSCase] * 
       y::ll<m>@M[Orig][LHSCase] & x!=null & {FLOW,(20,21)=__norm}
         EAssume 1::
           EXISTS(z_591: x::ll<z_591>@M[Orig][LHSCase] & A(n,m,z_591) & 
           0<=n & 0<=m & {FLOW,(20,21)=__norm})
NEW RELS: [ ( (m=0 | 1<=m) & 1+m=z & n=1) -->  A(n,m,z), ( 2<=z & 0<=m & 1<=n & A(n - 1,m,z - 1)) -->  A(n,m,z)]

Procedure append$node~node SUCCESS
Stop Omega... 84 invocations 
0 false contexts at: ()

Total verification time: 0.36 second(s)
	Time spent in main process: 0.34 second(s)
	Time spent in child processes: 0.02 second(s)

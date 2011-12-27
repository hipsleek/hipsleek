
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
           EXISTS(z_593: x::ll<z_593>@M[Orig][LHSCase] & A(n,m,z_593) & 
           0<=n & 0<=m & {FLOW,(20,21)=__norm})
NEW RELS: [ ( (m=0 | 1<=m) & flted_7_539+1=n & flted_7_539=0) -->  A(n,m,z_566), ( 0<=m_556 & 0<=n_555 & n_555=flted_7_539 & 1<=z_579 & flted_7_539+1=n & 
m_556=m & A(n_555,m_556,z_579)) -->  A(n,m,z_580)]

Procedure append$node~node SUCCESS
Stop Omega... 83 invocations 
0 false contexts at: ()

Total verification time: 0.396024 second(s)
	Time spent in main process: 0.368023 second(s)
	Time spent in child processes: 0.028001 second(s)

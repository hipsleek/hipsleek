
Processing file "dll-insert.ss"
Parsing dll-insert.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure insert$node2~int... 
Inferred Heap:[]
Inferred Pure:[ x!=null, x!=null]

INF-POST-FLAG: false
REL :  A(m,n)
POST:  n>=1 & n+1=m
PRE :  1<=n
OLD SPECS:  EInfer [x,A]
   EBase exists (Expl)(Impl)[p; n](ex)x::dll<p,n>@M[Orig][LHSCase]&true&
         {FLOW,(20,21)=__norm}
           EBase true&MayLoop&{FLOW,(1,23)=__flow}
                   EAssume 1::
                     EXISTS(p_25,m: x::dll<p_25,m>@M[Orig][LHSCase]&A(m,n) & 
                     p_25=p&{FLOW,(20,21)=__norm})
NEW SPECS:  EBase exists (Expl)(Impl)[p; n](ex)x::dll<p,n>@M[Orig][LHSCase]&true&
       {FLOW,(20,21)=__norm}
         EBase true&x!=null & 1<=n & MayLoop&{FLOW,(1,23)=__flow}
                 EAssume 1::
                   x::dll<p_25,m>@M[Orig][LHSCase]&A(m,n) & p_25=p & 0<=n&
                   {FLOW,(20,21)=__norm}
NEW RELS: [ (n=1 & m=2) --> A(m,n), (m=m_635+1 & n_588=n-1 & 1<=m_635 & 1<=n & A(m_635,n_588)) --> A(m,n)]

Procedure insert$node2~int SUCCESS

Termination checking result:

Stop Omega... 162 invocations 
0 false contexts at: ()

Total verification time: 0.37 second(s)
	Time spent in main process: 0.28 second(s)
	Time spent in child processes: 0.09 second(s)


Processing file "r1-i.ss"
Parsing r1-i.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure append$node~node... 
Inferred Heap:[]
Inferred Pure:[ n!=0, n!=0]

INF-POST-FLAG: true
REL :  A(n,m,z)
POST:  n>=1 & m>=0 & n+m=z
PRE :  1<=n & 0<=m
OLD SPECS:  EInfer [n,A]
   EBase exists (Expl)(Impl)[n; m](ex)x::ll<n>@M[Orig][LHSCase] * 
         y::ll<m>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
           EBase true&MayLoop&{FLOW,(1,23)=__flow}
                   EAssume 6::
                     EXISTS(z: x::ll<z>@M[Orig][LHSCase]&A(n,m,z)&
                     {FLOW,(20,21)=__norm})
NEW SPECS:  EBase exists (Expl)(Impl)[n; m](ex)x::ll<n>@M[Orig][LHSCase] * 
       y::ll<m>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
         EBase true&1<=n & 0<=m & MayLoop&{FLOW,(1,23)=__flow}
                 EAssume 6::
                   x::ll<z>@M[Orig][LHSCase]&n>=1 & m>=0 & n+m=z & 0<=n & 
                   0<=m&{FLOW,(20,21)=__norm}
NEW RELS: [ (n=1 & m=z-1 & 1<=z) --> A(n,m,z), (z=z_609+1 & m_587=m & n_586=n-1 & 1<=z_609 & 0<=m & 1<=n & 
  A(n_586,m_587,z_609)) --> A(n,m,z)]

Procedure append$node~node SUCCESS
Checking procedure foo$node... 
INF-POST-FLAG: true
REL :  F(res,n)
POST:  n>=0 & 0=res
PRE :  0<=n
OLD SPECS:  EInfer [F]
   EBase exists (Expl)(Impl)[n](ex)x::ll<n>@L[Orig][LHSCase]&true&
         {FLOW,(20,21)=__norm}
           EBase true&MayLoop&{FLOW,(1,23)=__flow}
                   EAssume 4::
                     true&F(res,n)&{FLOW,(20,21)=__norm}
NEW SPECS:  EBase exists (Expl)(Impl)[n](ex)x::ll<n>@L[Orig][LHSCase]&true&
       {FLOW,(20,21)=__norm}
         EBase true&0<=n & MayLoop&{FLOW,(1,23)=__flow}
                 EAssume 4::
                   true&n>=0 & 0=res & 0<=n&{FLOW,(20,21)=__norm}
NEW RELS: [ (n=0 & res=0) --> F(res,n), (m_29'=res & n_649=n-1 & 1<=n & F(m_29',n_649)) --> F(res,n)]

Procedure foo$node SUCCESS
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
NEW RELS: [ (n=0 & res=0) --> R(res,n), (r_30'=res-1 & n_685=n-1 & 1<=n & R(r_30',n_685)) --> R(res,n)]

Procedure length$node SUCCESS

Termination checking result:

Stop Omega... 283 invocations 
0 false contexts at: ()

Total verification time: 0.49 second(s)
	Time spent in main process: 0.3 second(s)
	Time spent in child processes: 0.19 second(s)


Processing file "ll-del.ss"
Parsing ll-del.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure delete$node~int... 
Inferred Heap:[]
Inferred Pure:[ n!=1 | a!=1, n!=0 | a!=1, n!=0 | a<=1, n!=0 | 1<=a]

INF-POST-FLAG: true
REL :  B(n,a,m)
POST:  a>=1 & m>=a & m+1=n
PRE :  1<=a & a<n
OLD SPECS:  EInfer [n,a,B]
   EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]&true&
         {FLOW,(20,21)=__norm}
           EBase true&MayLoop&{FLOW,(1,23)=__flow}
                   EAssume 1::
                     EXISTS(m: x::ll<m>@M[Orig][LHSCase]&B(n,a,m)&
                     {FLOW,(20,21)=__norm})
NEW SPECS:  EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]&true&
       {FLOW,(20,21)=__norm}
         EBase true&1<=a & a<n & MayLoop&{FLOW,(1,23)=__flow}
                 EAssume 1::
                   x::ll<m>@M[Orig][LHSCase]&a>=1 & m>=a & m+1=n & 0<=n&
                   {FLOW,(20,21)=__norm}
NEW RELS: [ (a=1 & m=n-1 & 2<=n) --> B(n,a,m), ((v_int_46_623=a-1 & n=n_601+1 & m=m_622+1 & 0<=n_601 & 0<=m_622 & 2<=a | 
  v_int_46_623=a-1 & n=n_601+1 & m=m_622+1 & a<=0 & 0<=n_601 & 0<=m_622) & 
  B(n_601,v_int_46_623,m_622)) --> B(n,a,m)]

Procedure delete$node~int SUCCESS

Termination checking result:

Stop Omega... 179 invocations 
0 false contexts at: ()

Total verification time: 0.35 second(s)
	Time spent in main process: 0.24 second(s)
	Time spent in child processes: 0.11 second(s)

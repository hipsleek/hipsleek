
Processing file "dll-app.ss"
Parsing dll-app.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure append$node2~node2... 
INF-POST-FLAG: false
REL :  C(t,m,n)
POST:  m>=0 & t>=m & t=n+m
PRE :  0<=m & 0<=n
OLD SPECS:  EInfer [C]
   EBase exists (Expl)(Impl)[q; m; p; n](ex)x::dll<q,m>@M[Orig][LHSCase] * 
         y::dll<p,n>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
           EBase true&MayLoop&{FLOW,(1,23)=__flow}
                   EAssume 1::
                     EXISTS(Anon_12,t: res::dll<Anon_12,t>@M[Orig][LHSCase]&
                     C(t,m,n)&{FLOW,(20,21)=__norm})
NEW SPECS:  EBase exists (Expl)(Impl)[q; m; p; n](ex)x::dll<q,m>@M[Orig][LHSCase] * 
       y::dll<p,n>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
         EBase true&0<=m & 0<=n & MayLoop&{FLOW,(1,23)=__flow}
                 EAssume 1::
                   res::dll<Anon_12,t>@M[Orig][LHSCase]&C(t,m,n) & 0<=m & 
                   0<=n&{FLOW,(20,21)=__norm}
NEW RELS: [ (m=0 & t=n & 0<=n) --> C(t,m,n), (m=m_623+1 & n=n_625 & t=t_650+1 & 0<=m_623 & 0<=n_625 & 1<=t_650 & 
  C(t_650,m_623,n_625)) --> C(t,m,n), (t_646=0 & t=1 & n_625=n & m_623=m-1 & 0<=n & 1<=m & 
  C(t_646,m_623,n_625)) --> C(t,m,n)]

Procedure append$node2~node2 SUCCESS
Checking procedure append2$node2~node2... 
Inferred Heap:[]
Inferred Pure:[ m!=0, m!=0, m!=0]

INF-POST-FLAG: false
REL :  D(t,m,n,r,p,q)
POST:  m>=1 & n>=0 & q=r & m+n=t
PRE :  1<=m & 0<=n
OLD SPECS:  EInfer [m,D]
   EBase exists (Expl)(Impl)[q; m; p; n](ex)x::dll<q,m>@M[Orig][LHSCase] * 
         y::dll<p,n>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
           EBase true&MayLoop&{FLOW,(1,23)=__flow}
                   EAssume 9::
                     EXISTS(t,r: x::dll<r,t>@M[Orig][LHSCase]&D(t,m,n,r,p,q)&
                     {FLOW,(20,21)=__norm})
NEW SPECS:  EBase exists (Expl)(Impl)[q; m; p; n](ex)x::dll<q,m>@M[Orig][LHSCase] * 
       y::dll<p,n>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
         EBase true&1<=m & 0<=n & MayLoop&{FLOW,(1,23)=__flow}
                 EAssume 9::
                   x::dll<r,t>@M[Orig][LHSCase]&D(t,m,n,r,p,q) & 0<=m & 0<=n&
                   {FLOW,(20,21)=__norm}
NEW RELS: [ (m=1 & n=0 & r=q & t=1) --> D(t,m,n,r,p,q), (q=r & m=1 & t=n+1 & 1<=n) --> D(t,m,n,r,p,q), (m=1 & n=0 & r=q & t=1) --> D(t,m,n,r,p,q), (p=p_841 & r=q & t=t_919+1 & n_842=n & m_840=m-1 & r_920=q_839 & 1<=t_919 & 
  0<=n & 1<=m & q_839!=null & 
  D(t_919,m_840,n_842,r_920,p_841,q_839)) --> D(t,m,n,r,p,q)]

Procedure append2$node2~node2 SUCCESS

Termination checking result:

Stop Omega... 414 invocations 
0 false contexts at: ()

Total verification time: 0.97 second(s)
	Time spent in main process: 0.61 second(s)
	Time spent in child processes: 0.36 second(s)

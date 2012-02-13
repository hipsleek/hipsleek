
Processing file "dll-app-nn.ss"
Parsing dll-app-nn.ss ...
Parsing ../../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
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
                   EAssume 1::
                     EXISTS(t,r: x::dll<r,t>@M[Orig][LHSCase]&D(t,m,n,r,p,q)&
                     {FLOW,(20,21)=__norm})
NEW SPECS:  EBase exists (Expl)(Impl)[q; m; p; n](ex)x::dll<q,m>@M[Orig][LHSCase] * 
       y::dll<p,n>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
         EBase true&1<=m & 0<=n & MayLoop&{FLOW,(1,23)=__flow}
                 EAssume 1::
                   x::dll<r,t>@M[Orig][LHSCase]&D(t,m,n,r,p,q) & 0<=m & 0<=n&
                   {FLOW,(20,21)=__norm}
NEW RELS: [ (m=1 & n=0 & r=q & t=1) --> D(t,m,n,r,p,q), (q=r & m=1 & t=n+1 & 1<=n) --> D(t,m,n,r,p,q), (m=1 & n=0 & r=q & t=1) --> D(t,m,n,r,p,q), (p=p_633 & r=q & t=t_711+1 & n_634=n & m_632=m-1 & r_712=q_631 & 1<=t_711 & 
  0<=n & 1<=m & q_631!=null & 
  D(t_711,m_632,n_634,r_712,p_633,q_631)) --> D(t,m,n,r,p,q)]

Procedure append2$node2~node2 SUCCESS

Termination checking result:

Stop Omega... 255 invocations 
0 false contexts at: ()

Total verification time: 0.68 second(s)
	Time spent in main process: 0.43 second(s)
	Time spent in child processes: 0.25 second(s)

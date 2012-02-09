
Processing file "dll-app.ss"
Parsing dll-app.ss ...
Parsing ../../../prelude.ss ...
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
         y::dll<p,n>@M[Orig][LHSCase] & true & {FLOW,(20,21)=__norm}
           EBase true & MayLoop & {FLOW,(1,23)=__flow}
                   EAssume 1::
                     EXISTS(Anon_12,t: res::dll<Anon_12,t>@M[Orig][LHSCase] &
                     C(t,m,n) & {FLOW,(20,21)=__norm})
NEW SPECS:  EBase exists (Expl)(Impl)[q; m; p; n](ex)x::dll<q,m>@M[Orig][LHSCase] * 
       y::dll<p,n>@M[Orig][LHSCase] & true & {FLOW,(20,21)=__norm}
         EBase true & 0<=m & 0<=n & MayLoop & {FLOW,(1,23)=__flow}
                 EAssume 1::
                   res::dll<Anon_12,t>@M[Orig][LHSCase] & C(t,m,n) & 0<=m & 
                   0<=n & {FLOW,(20,21)=__norm}
NEW RELS: [ ( m=0 & t=n & 0<=n) -->  C(t,m,n), ( m=m_584+1 & n=n_586 & t=t_611+1 & 0<=m_584 & 0<=n_586 & 1<=t_611 & 
C(t_611,m_584,n_586)) -->  C(t,m,n), ( t_607=0 & t=1 & n_586=n & m_584=m - 1 & 0<=n & 1<=m & C(t_607,m_584,n_586)) -->  C(t,m,n)]

Procedure append$node2~node2 SUCCESS

Termination checking result:

Stop Omega... 147 invocations 
0 false contexts at: ()

Total verification time: 0.38 second(s)
	Time spent in main process: 0.3 second(s)
	Time spent in child processes: 0.08 second(s)

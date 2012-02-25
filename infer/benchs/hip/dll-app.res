
Processing file "dll-app.ss"
Parsing dll-app.ss ...
Parsing ../../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure append$node2~node2... 
!!! REL :  C(t,m,n)
!!! POST:  n>=0 & t>=n & t=m+n
!!! PRE :  0<=n & 0<=m
!!! OLD SPECS: ((None,[]),EInfer [C]
              EBase exists (Expl)(Impl)[q; m; p; 
                    n](ex)x::dll<q,m>@M[Orig][LHSCase] * 
                    y::dll<p,n>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::
                                EXISTS(Anon_12,
                                t: res::dll<Anon_12,t>@M[Orig][LHSCase]&
                                C(t,m,n)&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[q; m; p; 
                  n](ex)x::dll<q,m>@M[Orig][LHSCase] * 
                  y::dll<p,n>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                    EBase true&0<=n & 0<=m & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 1::
                              res::dll<Anon_12,t>@M[Orig][LHSCase]&n>=0 & 
                              t>=n & t=m+n & 0<=m & 0<=n&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (t=n & 0<=n & m=0) --> C(t,m,n),
 (exists(flted_12_644:(t=2 & t_611=1 | 2+flted_12_644=t & 1+t_611=t & 
  3<=t) & C(t_611,m_584,n_586) & 1<=m & 0<=n & n_586=n & 1+
  m_584=m)) --> C(t,m,n),
 (t_607=0 & 1+m_584=m & n_586=n & t=1 & 0<=n & 1<=m & 
  C(t_607,m_584,n_586)) --> C(t,m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append$node2~node2 SUCCESS

Termination checking result:

Stop Omega... 119 invocations 
0 false contexts at: ()

Total verification time: 0.45 second(s)
	Time spent in main process: 0.34 second(s)
	Time spent in child processes: 0.11 second(s)

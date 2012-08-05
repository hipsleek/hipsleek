
Processing file "dll-app.ss"
Parsing dll-app.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure append$node2~node2... 
!!! REL :  C(t,m,n)
!!! POST:  m>=0 & n>=0 & m+n=t
!!! PRE :  true
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
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 1::
                              EXISTS(Anon_713,
                              t_714: res::dll<Anon_713,t_714>@M[Orig][LHSCase]&
                              m>=0 & n>=0 & m+n=t_714 & 0<=m & 0<=n&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (m=0 & n=t & 0<=t) --> C(t,m,n),
 (m_584=m-1 & n_586=n & t=t_611+1 & 1<=m & 0<=n & 1<=t_611 & 
  C(t_611,m_584,n_586)) --> C(t,m,n),
 (t_607=0 & t=1 & n=n_586 & m=m_584+1 & 0<=n_586 & 0<=m_584 & 
  C(t_607,m_584,n_586)) --> C(t,m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append$node2~node2 SUCCESS

Termination checking result:

Stop Omega... 122 invocations 
0 false contexts at: ()

Total verification time: 0.13 second(s)
	Time spent in main process: 0.06 second(s)
	Time spent in child processes: 0.07 second(s)

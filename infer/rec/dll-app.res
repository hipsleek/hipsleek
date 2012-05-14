
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
                              EXISTS(Anon_753,
                              t_754: res::dll<Anon_753,t_754>@M[Orig][LHSCase]&
                              m>=0 & n>=0 & m+n=t_754 & 0<=m & 0<=n&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (m=0 & n=t & 0<=t) --> C(t,m,n),
 (m_624=m-1 & n_626=n & t=t_651+1 & 1<=m & 0<=n & 1<=t_651 & 
  C(t_651,m_624,n_626)) --> C(t,m,n),
 (t_647=0 & t=1 & n=n_626 & m=m_624+1 & 0<=n_626 & 0<=m_624 & 
  C(t_647,m_624,n_626)) --> C(t,m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append$node2~node2 SUCCESS

Checking procedure append2$node2~node2... 
!!! REL :  D(t,m,n,r,p,q)
!!! POST:  m>=1 & t>=m & q=r & t=n+m
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [D]
              EBase exists (Expl)(Impl)[q; m; p; 
                    n](ex)x::dll<q,m>@M[Orig][LHSCase] * 
                    y::dll<p,n>@M[Orig][LHSCase]&1<=m&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 9::
                                EXISTS(t,r: x::dll<r,t>@M[Orig][LHSCase]&
                                D(t,m,n,r,p,q)&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[q; m; p; 
                  n](ex)x::dll<q,m>@M[Orig][LHSCase] * 
                  y::dll<p,n>@M[Orig][LHSCase]&1<=m&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 9::
                              EXISTS(t_943,
                              r_944: x::dll<r_944,t_943>@M[Orig][LHSCase]&
                              m>=1 & t_943>=m & q=r_944 & t_943=n+m & 0<=m & 
                              0<=n&{FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (r=q & m=1 & t=n+1 & 1<=n) --> D(t,m,n,r,p,q),
 (m=1 & n=0 & q=r & t=1) --> D(t,m,n,r,p,q),
 (p_842=p & t_917=t-1 & q=r & m=m_841+1 & n=n_843 & 2<=t & q_840!=null & 
  0<=m_841 & 0<=n_843 & 
  D(t_917,m_841,n_843,r_918,p_842,q_840)) --> D(t,m,n,r,p,q)]
!!! NEW ASSUME:[ RELASS [D]: ( D(t_917,m_841,n_843,r_918,p_842,q_840)) -->  r_918=q_840 | (r_918+1)<=q_840 & q_840=null | q_840<=(r_918-1) & q_840=null]
!!! NEW RANK:[]
Procedure append2$node2~node2 SUCCESS

Termination checking result:

Stop Omega... 214 invocations 
0 false contexts at: ()

Total verification time: 0.26 second(s)
	Time spent in main process: 0.09 second(s)
	Time spent in child processes: 0.17 second(s)

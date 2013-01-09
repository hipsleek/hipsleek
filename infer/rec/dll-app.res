Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure append$node2~node2... 
!!! REL :  C(t,m,n)
!!! POST:  m>=0 & n>=0 & t=m+n
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [C]
              EBase exists (Expl)(Impl)[q; m; p; 
                    n](ex)x::dll<q,m>@M[Orig][LHSCase] * 
                    y::dll<p,n>@M[Orig][LHSCase]&true&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 74::
                                EXISTS(Anon_19,
                                t: res::dll<Anon_19,t>@M[Orig][LHSCase]&
                                C(t,m,n)&{FLOW,(22,23)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[q; m; p; 
                  n](ex)x::dll<q,m>@M[Orig][LHSCase] * 
                  y::dll<p,n>@M[Orig][LHSCase]&true&{FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 74::
                              EXISTS(Anon_19,
                              t: res::dll<Anon_19,t>@M[Orig][LHSCase]&m>=0 & 
                              n>=0 & t=m+n&{FLOW,(22,23)=__norm})[])
!!! NEW RELS:[ (m=0 & n=t & 0<=t) --> C(t,m,n),
 (m_661=m-1 & n=n_663 & t=t_680+1 & 1<=m & 0<=n_663 & 1<=t_680 & 
  C(t_680,m_661,n_663)) --> C(t,m,n),
 (t_676=0 & t=1 & n=n_663 & m=m_661+1 & 0<=m_661 & 0<=n & 
  C(t_676,m_661,n_663)) --> C(t,m,n)]
!!! NEW ASSUME:[]
Procedure append$node2~node2 SUCCESS

Checking procedure append2$node2~node2... 
!!! REL :  D(t,m,n)
!!! POST:  m>=1 & n>=0 & t=m+n
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [D]
              EBase exists (Expl)(Impl)[q; m; p; 
                    n](ex)x::dll<q,m>@M[Orig][LHSCase] * 
                    y::dll<p,n>@M[Orig][LHSCase]&1<=m&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 82::
                                EXISTS(q_37,
                                t: x::dll<q_37,t>@M[Orig][LHSCase]&
                                D(t,m,n) & q=q_37&{FLOW,(22,23)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[q; m; p; 
                  n](ex)x::dll<q,m>@M[Orig][LHSCase] * 
                  y::dll<p,n>@M[Orig][LHSCase]&1<=m&{FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 82::
                              EXISTS(q_37,t: x::dll<q_37,t>@M[Orig][LHSCase]&
                              q=q_37 & m>=1 & n>=0 & t=m+n&
                              {FLOW,(22,23)=__norm})[])
!!! NEW RELS:[ (m=1 & t=n+1 & 1<=n) --> D(t,m,n),
 (n=0 & m=1 & t=1) --> D(t,m,n),
 (m=m_940+1 & n=n_942 & t_1001=t-1 & 0<=n & 0<=m_940 & 2<=t & 
  D(t_1001,m_940,n_942)) --> D(t,m,n)]
!!! NEW ASSUME:[]
Procedure append2$node2~node2 SUCCESS

Termination checking result:

Stop Omega... 186 invocations 
0 false contexts at: ()

Total verification time: 0.71 second(s)
	Time spent in main process: 0.51 second(s)
	Time spent in child processes: 0.2 second(s)


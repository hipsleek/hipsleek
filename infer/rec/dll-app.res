Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure append$node2~node2... 
!!! REL :  C(t,m,n)
!!! POST:  m>=0 & n>=0 & m+n=t
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [C]
              EBase exists (Expl)(Impl)[q; m; p; 
                    n](ex)x::dll<q,m>@M[Orig][LHSCase] * 
                    y::dll<p,n>@M[Orig][LHSCase]&true&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 74::
                                EXISTS(Anon_14,
                                t: res::dll<Anon_14,t>@M[Orig][LHSCase]&
                                C(t,m,n)&{FLOW,(22,23)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[q; m; p; 
                  n](ex)x::dll<q,m>@M[Orig][LHSCase] * 
                  y::dll<p,n>@M[Orig][LHSCase]&true&{FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 74::
                              EXISTS(Anon_14,
                              t: res::dll<Anon_14,t>@M[Orig][LHSCase]&m>=0 & 
                              n>=0 & m+n=t&{FLOW,(22,23)=__norm})[])
!!! NEW RELS:[ (m=0 & n=t & 0<=t) --> C(t,m,n),
 (m_652=m-1 & n=n_654 & t=t_673+1 & 1<=m & 0<=n_654 & 1<=t_673 & 
  C(t_673,m_652,n_654)) --> C(t,m,n),
 (t_669=0 & n_654=n & t=1 & m=m_652+1 & 0<=n & 0<=m_652 & 
  C(t_669,m_652,n_654)) --> C(t,m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append$node2~node2 SUCCESS

Checking procedure append2$node2~node2... 
!!! REL :  D(t,m,n)
!!! POST:  m>=1 & t>=m & t=n+m
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [D]
              EBase exists (Expl)(Impl)[q; m; p; 
                    n](ex)x::dll<q,m>@M[Orig][LHSCase] * 
                    y::dll<p,n>@M[Orig][LHSCase]&1<=m&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 82::
                                EXISTS(q_27,
                                t: x::dll<q_27,t>@M[Orig][LHSCase]&
                                D(t,m,n) & q_27=q&{FLOW,(22,23)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[q; m; p; 
                  n](ex)x::dll<q,m>@M[Orig][LHSCase] * 
                  y::dll<p,n>@M[Orig][LHSCase]&1<=m&{FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 82::
                              EXISTS(q_27,t: x::dll<q_27,t>@M[Orig][LHSCase]&
                              q_27=q & m>=1 & t>=m & t=n+m&
                              {FLOW,(22,23)=__norm})[])
!!! NEW RELS:[ (m=1 & t=n+1 & 1<=n) --> D(t,m,n),
 (m=1 & n=0 & t=1) --> D(t,m,n),
 (n_861=n & t_920=t-1 & m=m_859+1 & 2<=t & 0<=n & 0<=m_859 & 
  D(t_920,m_859,n_861)) --> D(t,m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append2$node2~node2 SUCCESS

Termination checking result:

Stop Omega... 148 invocations 
0 false contexts at: ()

Total verification time: 0.66 second(s)
	Time spent in main process: 0.53 second(s)
	Time spent in child processes: 0.13 second(s)

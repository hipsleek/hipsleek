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
 (m_653=m-1 & n=n_655 & t=t_674+1 & 1<=m & 0<=n_655 & 1<=t_674 & 
  C(t_674,m_653,n_655)) --> C(t,m,n),
 (t_670=0 & n_655=n & t=1 & m=m_653+1 & 0<=n & 0<=m_653 & 
  C(t_670,m_653,n_655)) --> C(t,m,n)]
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
                    y::dll<p,n>@M[Orig][LHSCase]&1<=m&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 82::
                                EXISTS(t,r: x::dll<r,t>@M[Orig][LHSCase]&
                                D(t,m,n,r,p,q)&{FLOW,(22,23)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[q; m; p; 
                  n](ex)x::dll<q,m>@M[Orig][LHSCase] * 
                  y::dll<p,n>@M[Orig][LHSCase]&1<=m&{FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 82::
                              EXISTS(t,r: x::dll<r,t>@M[Orig][LHSCase]&
                              m>=1 & t>=m & q=r & t=n+m&
                              {FLOW,(22,23)=__norm})[])
!!! NEW RELS:[ (r=q & m=1 & t=n+1 & 1<=n) --> D(t,m,n,r,p,q),
 (m=1 & n=0 & q=r & t=1) --> D(t,m,n,r,p,q),
 (p_861=p & n_862=n & t_922=t-1 & q=r & m=m_860+1 & 2<=t & 0<=n & 
  q_859!=null & 0<=m_860 & 
  D(t_922,m_860,n_862,r_923,p_861,q_859)) --> D(t,m,n,r,p,q)]
!!! NEW ASSUME:[ RELASS [D]: ( D(t_922,m_860,n_862,r_923,p_861,q_859)) -->  r_923=q_859 | q_859<r_923 & n_862<=(0-1) | q_859<r_923 & t_922<=0 & 
0<=n_862 | q_859<r_923 & m_860<=(0-1) & 0<=n_862 & 1<=t_922 | q_859<=(r_923-
1) & q_859=null & 0<=n_862 & 1<=t_922 & 0<=m_860 | n_862<=(0-1) & 
r_923<q_859 | t_922<=0 & r_923<q_859 & 0<=n_862 | m_860<=(0-1) & 
r_923<q_859 & 0<=n_862 & 1<=t_922 | (r_923+1)<=q_859 & q_859=null & 
0<=n_862 & 1<=t_922 & 0<=m_860]
!!! NEW RANK:[]
Procedure append2$node2~node2 SUCCESS

Termination checking result:

Stop Omega... 165 invocations 
0 false contexts at: ()

Total verification time: 0.79 second(s)
	Time spent in main process: 0.55 second(s)
	Time spent in child processes: 0.24 second(s)

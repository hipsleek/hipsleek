Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure append$node2~node2... 
!!! REL :  C(t,m,n)
!!! POST:  m>=0 & n>=0 & m+n=t
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [C]
              EBase exists (Expl)(Impl)[q; m; p; 
                    n](ex)x::dll<q,m>@M[Orig][LHSCase] * 
                    y::dll<p,n>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}[]
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                              EAssume 74::
                                EXISTS(Anon_14,
                                t: res::dll<Anon_14,t>@M[Orig][LHSCase]&
                                C(t,m,n)&{FLOW,(20,21)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[q; m; p; 
                  n](ex)x::dll<q,m>@M[Orig][LHSCase] * 
                  y::dll<p,n>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}[]
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                            EAssume 74::
                              EXISTS(Anon_14,
                              t: res::dll<Anon_14,t>@M[Orig][LHSCase]&m>=0 & 
                              n>=0 & m+n=t&{FLOW,(20,21)=__norm})[])
!!! NEW RELS:[ (m=0 & n=t & 0<=t) --> C(t,m,n),
 (m_639=m-1 & n=n_641 & t=t_660+1 & 1<=m & 0<=n_641 & 1<=t_660 & 
  C(t_660,m_639,n_641)) --> C(t,m,n),
 (t_656=0 & n_641=n & t=1 & m=m_639+1 & 0<=n & 0<=m_639 & 
  C(t_656,m_639,n_641)) --> C(t,m,n)]
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
                    y::dll<p,n>@M[Orig][LHSCase]&1<=m&{FLOW,(20,21)=__norm}[]
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                              EAssume 82::
                                EXISTS(t,r: x::dll<r,t>@M[Orig][LHSCase]&
                                D(t,m,n,r,p,q)&{FLOW,(20,21)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[q; m; p; 
                  n](ex)x::dll<q,m>@M[Orig][LHSCase] * 
                  y::dll<p,n>@M[Orig][LHSCase]&1<=m&{FLOW,(20,21)=__norm}[]
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                            EAssume 82::
                              EXISTS(t,r: x::dll<r,t>@M[Orig][LHSCase]&
                              m>=1 & t>=m & q=r & t=n+m&
                              {FLOW,(20,21)=__norm})[])
!!! NEW RELS:[ (r=q & m=1 & t=n+1 & 1<=n) --> D(t,m,n,r,p,q),
 (m=1 & n=0 & q=r & t=1) --> D(t,m,n,r,p,q),
 (p_845=p & n_846=n & t_906=t-1 & q=r & m=m_844+1 & 2<=t & 0<=n & 
  q_843!=null & 0<=m_844 & 
  D(t_906,m_844,n_846,r_907,p_845,q_843)) --> D(t,m,n,r,p,q)]
!!! NEW ASSUME:[ RELASS [D]: ( D(t_906,m_844,n_846,r_907,p_845,q_843)) -->  r_907=q_843 | q_843<r_907 & n_846<=(0-1) | q_843<r_907 & t_906<=0 & 
0<=n_846 | q_843<r_907 & m_844<=(0-1) & 0<=n_846 & 1<=t_906 | q_843<=(r_907-
1) & q_843=null & 0<=n_846 & 1<=t_906 & 0<=m_844 | n_846<=(0-1) & 
r_907<q_843 | t_906<=0 & r_907<q_843 & 0<=n_846 | m_844<=(0-1) & 
r_907<q_843 & 0<=n_846 & 1<=t_906 | (r_907+1)<=q_843 & q_843=null & 
0<=n_846 & 1<=t_906 & 0<=m_844]
!!! NEW RANK:[]
Procedure append2$node2~node2 SUCCESS

Termination checking result:

Stop Omega... 172 invocations 
0 false contexts at: ()

Total verification time: 0.76 second(s)
	Time spent in main process: 0.53 second(s)
	Time spent in child processes: 0.23 second(s)

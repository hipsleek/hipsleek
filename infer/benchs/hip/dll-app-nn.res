
Processing file "dll-app-nn.ss"
Parsing dll-app-nn.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure append2$node2~node2... 
!!! REL :  D(t,m,n,r,p,q)
!!! POST:  m>=1 & t>=m & q=r & t=n+m
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [D]
              EBase exists (Expl)(Impl)[q; m; p; 
                    n](ex)x::dll<q,m>@M[Orig][LHSCase] * 
                    y::dll<p,n>@M[Orig][LHSCase]&1<=m&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::
                                EXISTS(t,r: x::dll<r,t>@M[Orig][LHSCase]&
                                D(t,m,n,r,p,q)&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[q; m; p; 
                  n](ex)x::dll<q,m>@M[Orig][LHSCase] * 
                  y::dll<p,n>@M[Orig][LHSCase]&1<=m&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 1::
                              EXISTS(t_735,
                              r_736: x::dll<r_736,t_735>@M[Orig][LHSCase]&
                              m>=1 & t_735>=m & q=r_736 & t_735=n+m & 0<=m & 
                              0<=n&{FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (r=q & m=1 & t=n+1 & 1<=n) --> D(t,m,n,r,p,q),
 (m=1 & n=0 & q=r & t=1) --> D(t,m,n,r,p,q),
 (p_634=p & t_709=t-1 & q=r & m=m_633+1 & n=n_635 & 2<=t & q_632!=null & 
  0<=m_633 & 0<=n_635 & 
  D(t_709,m_633,n_635,r_710,p_634,q_632)) --> D(t,m,n,r,p,q)]
!!! NEW ASSUME:[ RELASS [D]: ( D(t_709,m_633,n_635,r_710,p_634,q_632)) -->  r_710=q_632 | (r_710+1)<=q_632 & q_632=null | q_632<=(r_710-1) & q_632=null]
!!! NEW RANK:[]
Procedure append2$node2~node2 SUCCESS

Termination checking result:

Stop Omega... 137 invocations 
0 false contexts at: ()

Total verification time: 0.16 second(s)
	Time spent in main process: 0.06 second(s)
	Time spent in child processes: 0.1 second(s)

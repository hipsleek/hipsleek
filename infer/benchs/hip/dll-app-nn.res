
Processing file "dll-app-nn.ss"
Parsing dll-app-nn.ss ...
Parsing ../../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure append2$node2~node2... 
!!! REL :  D(t,m,n,r,p,q)
!!! POST:  n>=0 & t>=(1+n) & q=r & t=m+n
!!! PRE :  0<=n & 1<=m
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
                    EBase true&0<=n & 1<=m & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 1::
                              x::dll<r,t>@M[Orig][LHSCase]&n>=0 & t>=(1+n) & 
                              q=r & t=m+n & 0<=m & 0<=n&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(flted_12_623:(t=2 & n=1 | 2+flted_12_623=t & 1+n=t & 3<=t) & r=q & 
  m=1)) --> D(t,m,n,r,p,q),
 (m=1 & n=0 & r=q & t=1) --> D(t,m,n,r,p,q),
 (1<=t_709 & p=p_634 & 1+m_633=m & n_635=n & -1+t=t_709 & r=q & 1<=m & 
  0<=n & D(t_709,m_633,n_635,r_710,p_634,q_632) & 
  q_632!=null) --> D(t,m,n,r,p,q)]
!!! NEW ASSUME:[ RELASS [D]: ( D(t_709,m_633,n_635,r_710,p_634,q_632)) -->  r_710=q_632 | (r_710+1)<=q_632 & q_632=null | q_632<=(r_710-1) & q_632=null]
!!! NEW RANK:[]
Procedure append2$node2~node2 SUCCESS

Termination checking result:

Stop Omega... 136 invocations 
0 false contexts at: ()

Total verification time: 0.41 second(s)
	Time spent in main process: 0.28 second(s)
	Time spent in child processes: 0.13 second(s)

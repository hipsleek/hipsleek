
Processing file "dll-app.ss"
Parsing dll-app.ss ...
Parsing ../../prelude.ss ...
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
                              EXISTS(Anon_753,
                              t_754: res::dll<Anon_753,t_754>@M[Orig][LHSCase]&
                              n>=0 & t_754>=n & t_754=m+n & 0<=m & 0<=n&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (t=n & 0<=n & m=0) --> C(t,m,n),
 (exists(flted_12_684:(t=2 & t_651=1 | 2+flted_12_684=t & 1+t_651=t & 
  3<=t) & C(t_651,m_624,n_626) & 1<=m & 0<=n & n_626=n & 1+
  m_624=m)) --> C(t,m,n),
 (t_647=0 & 1+m_624=m & n_626=n & t=1 & 0<=n & 1<=m & 
  C(t_647,m_624,n_626)) --> C(t,m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append$node2~node2 SUCCESS

Checking procedure append2$node2~node2... 
!!! REL :  D(t,m,n,r,p,q)
!!! POST:  n>=0 & t>=(1+n) & q=r & t=m+n
!!! PRE :  0<=n & 1<=m
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
                    EBase true&0<=n & 1<=m & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 9::
                              EXISTS(t_943,
                              r_944: x::dll<r_944,t_943>@M[Orig][LHSCase]&
                              n>=0 & t_943>=(1+n) & q=r_944 & t_943=m+n & 
                              0<=m & 0<=n&{FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(flted_12_831:(t=2 & n=1 | 2+flted_12_831=t & 1+n=t & 3<=t) & r=q & 
  m=1)) --> D(t,m,n,r,p,q),
 (m=1 & n=0 & r=q & t=1) --> D(t,m,n,r,p,q),
 (1<=t_917 & p=p_842 & 1+m_841=m & n_843=n & -1+t=t_917 & r=q & 1<=m & 
  0<=n & D(t_917,m_841,n_843,r_918,p_842,q_840) & 
  q_840!=null) --> D(t,m,n,r,p,q)]
!!! NEW ASSUME:[ RELASS [D]: ( D(t_917,m_841,n_843,r_918,p_842,q_840)) -->  r_918=q_840 | (r_918+1)<=q_840 & q_840=null | q_840<=(r_918-1) & q_840=null]
!!! NEW RANK:[]
Procedure append2$node2~node2 SUCCESS

Termination checking result:

Stop Omega... 211 invocations 
0 false contexts at: ()

Total verification time: 0.76 second(s)
	Time spent in main process: 0.56 second(s)
	Time spent in child processes: 0.2 second(s)


Processing file "dll-del.ss"
Parsing dll-del.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure delete$node2~int... 
!!! REL :  B(m,n)
!!! POST:  m>=1 & m+1=n
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [B]
              EBase exists (Expl)(Impl)[p; 
                    n](ex)x::dll<p,n>@M[Orig][LHSCase]&a<n & 0<a&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::
                                EXISTS(p_28,
                                m: x::dll<p_28,m>@M[Orig][LHSCase]&B(m,n) & 
                                p_28=p&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p; n](ex)x::dll<p,n>@M[Orig][LHSCase]&
                  1<=a & a<n&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 1::
                              EXISTS(p_826,
                              m_827: x::dll<p_826,m_827>@M[Orig][LHSCase]&
                              p_826=p & m_827>=1 & m_827+1=n & 0<=n&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (m=n-1 & 3<=n) --> B(m,n),
 (n=2 & m=1) --> B(m,n),
 (m=m_800+1 & n_734=n-1 & 3<=n & 0<=m_800 & B(m_800,n_734)) --> B(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete$node2~int SUCCESS

Termination checking result:

Stop Omega... 121 invocations 
0 false contexts at: ()

Total verification time: 0.11 second(s)
	Time spent in main process: 0.06 second(s)
	Time spent in child processes: 0.05 second(s)

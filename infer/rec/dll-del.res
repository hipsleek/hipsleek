Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure delete$node2~int... 
!!! REL :  B(m,n)
!!! POST:  m>=1 & m+1=n
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [B]
              EBase exists (Expl)(Impl)[p; 
                    n](ex)x::dll<p,n>@M[Orig][LHSCase]&a<n & 0<a&
                    {FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 69::
                                EXISTS(p_25,
                                m: x::dll<p_25,m>@M[Orig][LHSCase]&B(m,n) & 
                                p_25=p&{FLOW,(22,23)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p; n](ex)x::dll<p,n>@M[Orig][LHSCase]&
                  1<=a & a<n&{FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 69::
                              EXISTS(p_25,m: x::dll<p_25,m>@M[Orig][LHSCase]&
                              p_25=p & m>=1 & m+1=n&{FLOW,(22,23)=__norm})[])
!!! NEW RELS:[ (m=n-1 & 3<=n) --> B(m,n),
 (n=2 & m=1) --> B(m,n),
 (m=m_826+1 & n_766=n-1 & 3<=n & 0<=m_826 & B(m_826,n_766)) --> B(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete$node2~int SUCCESS

Termination checking result:

Stop Omega... 103 invocations 
0 false contexts at: ()

Total verification time: 0.45 second(s)
	Time spent in main process: 0.39 second(s)
	Time spent in child processes: 0.06 second(s)

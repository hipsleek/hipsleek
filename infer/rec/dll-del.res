Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure delete$node2~int... 
!!! REL :  B(m,n)
!!! POST:  m>=1 & n=m+1
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [B]
              EBase exists (Expl)(Impl)[p; 
                    n](ex)x::dll<p,n>@M[Orig][LHSCase]&a<n & 0<a&
                    {FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 69::
                                EXISTS(p_31,
                                m: x::dll<p_31,m>@M[Orig][LHSCase]&B(m,n) & 
                                p=p_31&{FLOW,(22,23)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p; n](ex)x::dll<p,n>@M[Orig][LHSCase]&
                  1<=a & a<n&{FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 69::
                              EXISTS(p_31,m: x::dll<p_31,m>@M[Orig][LHSCase]&
                              p=p_31 & m>=1 & n=m+1&{FLOW,(22,23)=__norm})[])
!!! NEW RELS:[ (m=n-1 & 3<=n) --> B(m,n),
 (m=1 & n=2) --> B(m,n),
 (m=m_825+1 & n_765=n-1 & 3<=n & 0<=m_825 & B(m_825,n_765)) --> B(m,n)]
!!! NEW ASSUME:[]
Procedure delete$node2~int SUCCESS

Termination checking result:

Stop Omega... 112 invocations 
0 false contexts at: ()

Total verification time: 0.54 second(s)
	Time spent in main process: 0.4 second(s)
	Time spent in child processes: 0.14 second(s)


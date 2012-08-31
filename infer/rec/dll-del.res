Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure delete$node2~int... 
!!! REL :  B(m,n)
!!! POST:  m>=1 & m+1=n
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [B]
              EBase exists (Expl)(Impl)[p; 
                    n](ex)x::dll<p,n>@M[Orig][LHSCase]&a<n & 0<a&
                    {FLOW,(20,21)=__norm}[]
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                              EAssume 69::
                                EXISTS(p_29,
                                m: x::dll<p_29,m>@M[Orig][LHSCase]&B(m,n) & 
                                p_29=p&{FLOW,(20,21)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p; n](ex)x::dll<p,n>@M[Orig][LHSCase]&
                  1<=a & a<n&{FLOW,(20,21)=__norm}[]
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                            EAssume 69::
                              EXISTS(p_29,m: x::dll<p_29,m>@M[Orig][LHSCase]&
                              p_29=p & m>=1 & m+1=n&{FLOW,(20,21)=__norm})[])
!!! NEW RELS:[ (m=n-1 & 3<=n) --> B(m,n),
 (n=2 & m=1) --> B(m,n),
 (m=m_808+1 & n_748=n-1 & 3<=n & 0<=m_808 & B(m_808,n_748)) --> B(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete$node2~int SUCCESS

Termination checking result:

Stop Omega... 107 invocations 
0 false contexts at: ()

Total verification time: 0.41 second(s)
	Time spent in main process: 0.36 second(s)
	Time spent in child processes: 0.05 second(s)

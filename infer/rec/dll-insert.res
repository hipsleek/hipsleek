Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure insert$node2~int... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null, x!=null]
!!! REL :  A(m,n)
!!! POST:  m>=2 & m=n+1
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [x,A]
              EBase exists (Expl)(Impl)[p; 
                    n](ex)x::dll<p,n>@M[Orig][LHSCase]&true&
                    {FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 64::
                                EXISTS(p_31,
                                m: x::dll<p_31,m>@M[Orig][LHSCase]&A(m,n) & 
                                p=p_31&{FLOW,(22,23)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p; n](ex)x::dll<p,n>@M[Orig][LHSCase]&
                  true&{FLOW,(22,23)=__norm}[]
                    EBase emp&x!=null & MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 64::
                              EXISTS(p_31,m: x::dll<p_31,m>@M[Orig][LHSCase]&
                              p=p_31 & m>=2 & m=n+1&{FLOW,(22,23)=__norm})[])
!!! NEW RELS:[ (m=2 & n=1) --> A(m,n),
 (n=n_621+1 & m_668=m-1 & 0<=n_621 & 2<=m & A(m_668,n_621)) --> A(m,n)]
!!! NEW ASSUME:[]
Procedure insert$node2~int SUCCESS

Termination checking result:

Stop Omega... 96 invocations 
0 false contexts at: ()

Total verification time: 0.34 second(s)
	Time spent in main process: 0.27 second(s)
	Time spent in child processes: 0.07 second(s)


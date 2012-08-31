Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure insert$node2~int... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null, x!=null]
!!! REL :  A(m,n)
!!! POST:  n>=1 & n+1=m
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [x,A]
              EBase exists (Expl)(Impl)[p; 
                    n](ex)x::dll<p,n>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}[]
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                              EAssume 64::
                                EXISTS(p_26,
                                m: x::dll<p_26,m>@M[Orig][LHSCase]&A(m,n) & 
                                p_26=p&{FLOW,(20,21)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p; n](ex)x::dll<p,n>@M[Orig][LHSCase]&
                  true&{FLOW,(20,21)=__norm}[]
                    EBase true&x!=null & MayLoop&{FLOW,(1,23)=__flow}[]
                            EAssume 64::
                              EXISTS(p_26,m: x::dll<p_26,m>@M[Orig][LHSCase]&
                              p_26=p & n>=1 & n+1=m&{FLOW,(20,21)=__norm})[])
!!! NEW RELS:[ (n=1 & m=2) --> A(m,n),
 (m_646=m-1 & n=n_602+1 & 2<=m & 0<=n_602 & A(m_646,n_602)) --> A(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert$node2~int SUCCESS

Termination checking result:

Stop Omega... 83 invocations 
0 false contexts at: ()

Total verification time: 0.28 second(s)
	Time spent in main process: 0.24 second(s)
	Time spent in child processes: 0.04 second(s)

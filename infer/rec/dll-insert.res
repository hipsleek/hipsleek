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
                    {FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 64::
                                EXISTS(p_25,
                                m: x::dll<p_25,m>@M[Orig][LHSCase]&A(m,n) & 
                                p_25=p&{FLOW,(22,23)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p; n](ex)x::dll<p,n>@M[Orig][LHSCase]&
                  true&{FLOW,(22,23)=__norm}[]
                    EBase emp&x!=null & MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 64::
                              EXISTS(p_25,m: x::dll<p_25,m>@M[Orig][LHSCase]&
                              p_25=p & n>=1 & n+1=m&{FLOW,(22,23)=__norm})[])
!!! NEW RELS:[ (n=1 & m=2) --> A(m,n),
 (m_670=m-1 & n=n_623+1 & 2<=m & 0<=n_623 & A(m_670,n_623)) --> A(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert$node2~int SUCCESS

Termination checking result:

Stop Omega... 79 invocations 
0 false contexts at: ()

Total verification time: 0.3 second(s)
	Time spent in main process: 0.26 second(s)
	Time spent in child processes: 0.04 second(s)

Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure insert$node~int... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ n!=0]
!!! REL :  A(m,n)
!!! POST:  m>=2 & m=n+1
!!! PRE :  1<=n
!!! OLD SPECS: ((None,[]),EInfer [n,A]
              EBase exists (Expl)(Impl)[n](ex)x::hd<n>@M[Orig][LHSCase]&true&
                    {FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 64::
                                EXISTS(m: x::hd<m>@M[Orig][LHSCase]&A(m,n)&
                                {FLOW,(22,23)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::hd<n>@M[Orig][LHSCase]&true&
                  {FLOW,(22,23)=__norm}[]
                    EBase emp&1<=n & MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 64::
                              EXISTS(m: x::hd<m>@M[Orig][LHSCase]&m>=2 & m=n+
                              1&{FLOW,(22,23)=__norm})[])
!!! NEW RELS:[ (m=n+1 & 1<=n) --> A(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert$node~int SUCCESS

Termination checking result:

Stop Omega... 92 invocations 
0 false contexts at: ()

Total verification time: 0.3 second(s)
	Time spent in main process: 0.22 second(s)
	Time spent in child processes: 0.08 second(s)

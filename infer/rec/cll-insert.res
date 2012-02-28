
Processing file "cll-insert.ss"
Parsing cll-insert.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure insert$node~int... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ n!=0]
!!! REL :  A(m,n)
!!! POST:  n>=1 & n+1=m
!!! PRE :  1<=n
!!! OLD SPECS: ((None,[]),EInfer [n,A]
              EBase exists (Expl)(Impl)[n](ex)x::hd<n>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::
                                EXISTS(m: x::hd<m>@M[Orig][LHSCase]&A(m,n)&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::hd<n>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&1<=n & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 1::
                              EXISTS(m_590: x::hd<m_590>@M[Orig][LHSCase]&
                              n>=1 & n+1=m_590 & 0<=n&{FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (m=n+1 & 1<=n) --> A(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert$node~int SUCCESS

Termination checking result:

Stop Omega... 107 invocations 
0 false contexts at: ()

Total verification time: 0.29 second(s)
	Time spent in main process: 0.17 second(s)
	Time spent in child processes: 0.12 second(s)


Processing file "cll-insert.ss"
Parsing cll-insert.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
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
                              m_590>=2 & m_590=n+1 & 0<=n&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (m=n+1 & 1<=n) --> A(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert$node~int SUCCESS

Termination checking result:

Stop Omega... 106 invocations 
0 false contexts at: ()

Total verification time: 0.15 second(s)
	Time spent in main process: 0.04 second(s)
	Time spent in child processes: 0.11 second(s)

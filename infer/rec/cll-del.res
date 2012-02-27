
Processing file "cll-del.ss"
Parsing cll-del.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure delete$node... 
!!! REL :  A(m,n)
!!! POST:  m>=0 & m+1=n
!!! PRE :  1<=n
!!! OLD SPECS: ((None,[]),EInfer [n,A]
              EBase exists (Expl)(Impl)[n](ex)x::hd<n>@M[Orig][LHSCase]&0<n&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::ref [x]
                                EXISTS(m: x'::hd<m>@M[Orig][LHSCase]&A(m,n)&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::hd<n>@M[Orig][LHSCase]&1<=n&
                  {FLOW,(20,21)=__norm}
                    EBase true&1<=n & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 1::ref [x]
                              EXISTS(m_628: x'::hd<m_628>@M[Orig][LHSCase]&
                              m_628>=0 & m_628+1=n & 0<=n&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(flted_11_599:m=1 & n=2 | -1+n=m & 1+flted_11_599=m & 
  2<=m)) --> A(m,n),
 (n=1 & m=0) --> A(m,n),
 (m=1 & n=2) --> A(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete$node SUCCESS

Termination checking result:

Stop Omega... 107 invocations 
0 false contexts at: ()

Total verification time: 0.34 second(s)
	Time spent in main process: 0.2 second(s)
	Time spent in child processes: 0.14 second(s)

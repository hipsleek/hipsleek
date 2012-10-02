Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure delete$node... 
!!! REL :  A(m,n)
!!! POST:  n>=1 & n=m+1
!!! PRE :  1<=n
!!! OLD SPECS: ((None,[]),EInfer [n,A]
              EBase exists (Expl)(Impl)[n](ex)x::hd<n>@M[Orig][LHSCase]&0<n&
                    {FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 66::ref [x]
                                EXISTS(m: x'::hd<m>@M[Orig][LHSCase]&A(m,n)&
                                {FLOW,(22,23)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::hd<n>@M[Orig][LHSCase]&1<=n&
                  {FLOW,(22,23)=__norm}[]
                    EBase emp&1<=n & MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 66::ref [x]
                              EXISTS(m: x'::hd<m>@M[Orig][LHSCase]&n>=1 & 
                              n=m+1&{FLOW,(22,23)=__norm})[])
!!! NEW RELS:[ (n=1 & m=0) --> A(m,n),
 (m=n-1 & 2<=n) --> A(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete$node SUCCESS

Termination checking result:

Stop Omega... 87 invocations 
0 false contexts at: ()

Total verification time: 0.28 second(s)
	Time spent in main process: 0.23 second(s)
	Time spent in child processes: 0.05 second(s)

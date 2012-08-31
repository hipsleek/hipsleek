Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure count$node... 
!!! REL :  A(res,n)
!!! POST:  n>=0 & n=res
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [A]
              EBase exists (Expl)(Impl)[n](ex)x::hd<n>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}[]
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                              EAssume 68::
                                EXISTS(n_31: x::hd<n_31>@M[Orig][LHSCase]&
                                A(res,n) & n_31=n&{FLOW,(20,21)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::hd<n>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}[]
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                            EAssume 68::
                              EXISTS(n_31: x::hd<n_31>@M[Orig][LHSCase]&
                              n_31=n & n>=0 & n=res&{FLOW,(20,21)=__norm})[])
!!! NEW RELS:[ (res=0 & n=0) --> A(res,n),
 (res=n & 1<=n) --> A(res,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure count$node SUCCESS

Termination checking result:

Stop Omega... 93 invocations 
0 false contexts at: ()

Total verification time: 0.28 second(s)
	Time spent in main process: 0.23 second(s)
	Time spent in child processes: 0.05 second(s)

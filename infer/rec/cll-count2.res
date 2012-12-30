Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure count$node... 
!!! REL :  A(res,n)
!!! POST:  n>=0 & n=res
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [A]
              EBase exists (Expl)(Impl)[n](ex)x::hd<n>@M[Orig][LHSCase]&true&
                    {FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 68::
                                EXISTS(n_29: x::hd<n_29>@M[Orig][LHSCase]&
                                A(res,n) & n_29=n&{FLOW,(22,23)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::hd<n>@M[Orig][LHSCase]&true&
                  {FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 68::
                              EXISTS(n_29: x::hd<n_29>@M[Orig][LHSCase]&
                              n_29=n & n>=0 & n=res&{FLOW,(22,23)=__norm})[])
!!! NEW RELS:[ (res=0 & n=0) --> A(res,n),
 (res=n & 1<=n) --> A(res,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure count$node SUCCESS

Termination checking result:

Stop Omega... 84 invocations 
0 false contexts at: ()

Total verification time: 0.28 second(s)
	Time spent in main process: 0.24 second(s)
	Time spent in child processes: 0.04 second(s)

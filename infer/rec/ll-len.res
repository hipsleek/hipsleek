Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure length$node... 
!!! REL :  R(res,n)
!!! POST:  res>=0 & res=n
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [R]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@L[Orig][LHSCase]&true&
                    {FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 64::
                                emp&R(res,n)&{FLOW,(22,23)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@L[Orig][LHSCase]&true&
                  {FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 64::
                              emp&res>=0 & res=n&{FLOW,(22,23)=__norm}[])
!!! NEW RELS:[ (n=0 & res=0) --> R(res,n),
 (res=r_585+1 & n_573=n-1 & 1<=n & R(r_585,n_573)) --> R(res,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure length$node SUCCESS

Termination checking result:

Stop Omega... 64 invocations 
0 false contexts at: ()

Total verification time: 0.24 second(s)
	Time spent in main process: 0.2 second(s)
	Time spent in child processes: 0.04 second(s)

Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure foo$node... 
!!! REL :  F(res,n)
!!! POST:  n>=0 & res=0
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [F]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@L[Orig][LHSCase]&true&
                    {FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 63::
                                emp&F(res,n)&{FLOW,(22,23)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@L[Orig][LHSCase]&true&
                  {FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 63::
                              emp&n>=0 & res=0&{FLOW,(22,23)=__norm}[])
!!! NEW RELS:[ (n=0 & res=0) --> F(res,n),
 (n_570=n-1 & 1<=n & F(res,n_570)) --> F(res,n)]
!!! NEW ASSUME:[]
Procedure foo$node SUCCESS

Termination checking result:

Stop Omega... 56 invocations 
0 false contexts at: ()

Total verification time: 0.25 second(s)
	Time spent in main process: 0.21 second(s)
	Time spent in child processes: 0.04 second(s)


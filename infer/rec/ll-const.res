Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure foo$node... 
!!! REL :  F(res,n)
!!! POST:  n>=0 & 0=res
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
                              emp&n>=0 & 0=res&{FLOW,(22,23)=__norm}[])
!!! NEW RELS:[ (n=0 & res=0) --> F(res,n),
 (v_int_22_539'=res & n_572=n-1 & 1<=n & F(v_int_22_539',n_572)) --> F(res,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure foo$node SUCCESS

Termination checking result:

Stop Omega... 62 invocations 
0 false contexts at: ()

Total verification time: 0.24 second(s)
	Time spent in main process: 0.2 second(s)
	Time spent in child processes: 0.04 second(s)

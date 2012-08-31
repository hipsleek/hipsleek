Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure length$node... 
!!! REL :  R(res,n)
!!! POST:  res>=0 & res=n
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [R]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@L[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}[]
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                              EAssume 64::
                                true&R(res,n)&{FLOW,(20,21)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@L[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}[]
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                            EAssume 64::
                              true&res>=0 & res=n&{FLOW,(20,21)=__norm}[])
!!! NEW RELS:[ (n=0 & res=0) --> R(res,n),
 (res=r_25'+1 & n_553=n-1 & 1<=n & R(r_25',n_553)) --> R(res,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure length$node SUCCESS

Termination checking result:

Stop Omega... 67 invocations 
0 false contexts at: ()

Total verification time: 0.23 second(s)
	Time spent in main process: 0.19 second(s)
	Time spent in child processes: 0.04 second(s)

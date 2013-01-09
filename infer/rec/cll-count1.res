Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure count$node~node... 
!!! REL :  A(res,n)
!!! POST:  n>=0 & n=res
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [A]
              EBase exists (Expl)(Impl)[p; 
                    n](ex)x::cll<p,n>@M[Orig][LHSCase]&h=p&
                    {FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 66::
                                EXISTS(p_35,
                                n_36: x::cll<p_35,n_36>@M[Orig][LHSCase]&
                                A(res,n) & p=p_35 & n=n_36&
                                {FLOW,(22,23)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p; n](ex)x::cll<p,n>@M[Orig][LHSCase]&
                  h=p&{FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 66::
                              EXISTS(p_35,
                              n_36: x::cll<p_35,n_36>@M[Orig][LHSCase]&
                              p=p_35 & n=n_36 & n>=0 & n=res&
                              {FLOW,(22,23)=__norm})[])
!!! NEW RELS:[ (res=0 & n=0) --> A(res,n),
 (n_623=res-1 & n_610=n-1 & 1<=n & A(n_623,n_610)) --> A(res,n)]
!!! NEW ASSUME:[]
Procedure count$node~node SUCCESS

Termination checking result:

Stop Omega... 99 invocations 
0 false contexts at: ()

Total verification time: 0.36 second(s)
	Time spent in main process: 0.28 second(s)
	Time spent in child processes: 0.08 second(s)


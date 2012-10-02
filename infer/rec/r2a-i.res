Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure length$node... 
!!! REL :  R(res,n)
!!! POST:  n>=0 & n=res
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [R]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@L[Orig][LHSCase]&true&
                    {FLOW,(22,23)=__norm}[]
                      ECase case {
                             n=0 -> ((None,[]),EBase emp&MayLoop&
                                                     {FLOW,(1,25)=__flow}[]
                                                       EAssume 65::
                                                         emp&R(res,n)&
                                                         {FLOW,(22,23)=__norm}[])
                             ;
                             n!=0 -> ((None,[]),EBase emp&MayLoop&
                                                      {FLOW,(1,25)=__flow}[]
                                                        EAssume 66::
                                                          emp&R(res,n)&
                                                          {FLOW,(22,23)=__norm}[])
                             
                             })
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@L[Orig][LHSCase]&true&
                  {FLOW,(22,23)=__norm}[]
                    ECase case {
                           n=0 -> ((None,[]),EBase emp&MayLoop&
                                                   {FLOW,(1,25)=__flow}[]
                                                     EAssume 65::
                                                       emp&n>=0 & n=res&
                                                       {FLOW,(22,23)=__norm}[])
                           ;
                           n!=0 -> ((None,[]),EBase emp&MayLoop&
                                                    {FLOW,(1,25)=__flow}[]
                                                      EAssume 66::
                                                        emp&n>=0 & n=res&
                                                        {FLOW,(22,23)=__norm}[])
                           
                           })
!!! NEW RELS:[ (n=0 & res=0) --> R(res,n),
 (n_590=0 & n=1 & r_605=res-1 & R(r_605,n_590)) --> R(res,n),
 (r_608=res-1 & n=n_590+1 & 1<=n_590 & R(r_608,n_590)) --> R(res,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure length$node SUCCESS

Termination checking result:

Stop Omega... 76 invocations 
9 false contexts at: ( (21,15)  (21,22)  (24,4)  (24,11)  (24,11)  (23,12)  (23,19)  (23,8)  (22,7) )

Total verification time: 0.27 second(s)
	Time spent in main process: 0.22 second(s)
	Time spent in child processes: 0.05 second(s)

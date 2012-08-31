Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure length$node... 
!!! REL :  R(res,n)
!!! POST:  n>=0 & n=res
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [R]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@L[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}[]
                      ECase case {
                             n=0 -> ((None,[]),EBase true&MayLoop&
                                                     {FLOW,(1,23)=__flow}[]
                                                       EAssume 65::
                                                         true&R(res,n)&
                                                         {FLOW,(20,21)=__norm}[])
                             ;
                             n!=0 -> ((None,[]),EBase true&MayLoop&
                                                      {FLOW,(1,23)=__flow}[]
                                                        EAssume 66::
                                                          true&R(res,n)&
                                                          {FLOW,(20,21)=__norm}[])
                             
                             })
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@L[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}[]
                    ECase case {
                           n=0 -> ((None,[]),EBase true&MayLoop&
                                                   {FLOW,(1,23)=__flow}[]
                                                     EAssume 65::
                                                       true&n>=0 & n=res&
                                                       {FLOW,(20,21)=__norm}[])
                           ;
                           n!=0 -> ((None,[]),EBase true&MayLoop&
                                                    {FLOW,(1,23)=__flow}[]
                                                      EAssume 66::
                                                        true&n>=0 & n=res&
                                                        {FLOW,(20,21)=__norm}[])
                           
                           })
!!! NEW RELS:[ (n=0 & res=0) --> R(res,n),
 (n_570=0 & n=1 & r_25'=res-1 & R(r_25',n_570)) --> R(res,n),
 (r_25'=res-1 & n=n_570+1 & 1<=n_570 & R(r_25',n_570)) --> R(res,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure length$node SUCCESS

Termination checking result:

Stop Omega... 81 invocations 
9 false contexts at: ( (21,15)  (21,22)  (24,4)  (24,11)  (24,11)  (23,12)  (23,19)  (23,8)  (23,4) )

Total verification time: 0.25 second(s)
	Time spent in main process: 0.2 second(s)
	Time spent in child processes: 0.05 second(s)

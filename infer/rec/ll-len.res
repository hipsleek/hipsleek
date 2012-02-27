
Processing file "ll-len.ss"
Parsing ll-len.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure length$node... 
!!! REL :  R(res,n)
!!! POST:  res>=0 & res=n
!!! PRE :  0<=n
!!! OLD SPECS: ((None,[]),EInfer [R]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@L[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::
                                true&R(res,n)&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@L[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&0<=n & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 1::
                              true&res>=0 & res=n & 0<=n&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (n=0 & res=0) --> R(res,n),
 (exists(flted_7_534:(n_539=0 & n=1 | flted_7_534=n_539 & -1+n=n_539 & 
  1<=n_539) & R(r_24',n_539) & -1+res=r_24')) --> R(res,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure length$node SUCCESS

Termination checking result:

Stop Omega... 72 invocations 
0 false contexts at: ()

Total verification time: 0.23 second(s)
	Time spent in main process: 0.17 second(s)
	Time spent in child processes: 0.06 second(s)

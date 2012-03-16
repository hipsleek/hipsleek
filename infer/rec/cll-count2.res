
Processing file "cll-count2.ss"
Parsing cll-count2.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure count$node... 
!!! REL :  A(res,n)
!!! POST:  n>=0 & n=res
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [A]
              EBase exists (Expl)(Impl)[n](ex)x::hd<n>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 2::
                                EXISTS(n_29: x::hd<n_29>@M[Orig][LHSCase]&
                                A(res,n) & n_29=n&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::hd<n>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 2::
                              EXISTS(n_1034: x::hd<n_1034>@M[Orig][LHSCase]&
                              n_1034=n & n>=0 & n=res & 0<=n&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (res=n & 1<=n) --> A(res,n),
 (res=0 & n=0) --> A(res,n),
 (n=1 & res=1) --> A(res,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure count$node SUCCESS

Termination checking result:

Stop Omega... 185 invocations 
0 false contexts at: ()

Total verification time: 0.18 second(s)
	Time spent in main process: 0.1 second(s)
	Time spent in child processes: 0.08 second(s)

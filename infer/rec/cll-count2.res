
Processing file "cll-count2.ss"
Parsing cll-count2.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure count$node... 
!!! REL :  A(res,n)
!!! POST:  res>=0 & res=n
!!! PRE :  0<=n
!!! OLD SPECS: ((None,[]),EInfer [A]
              EBase exists (Expl)(Impl)[n](ex)x::hd<n>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 2::
                                EXISTS(n_29: x::hd<n_29>@M[Orig][LHSCase]&
                                A(res,n) & n_29=n&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::hd<n>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&0<=n & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 2::
                              x::hd<n_29>@M[Orig][LHSCase]&A(res,n) & 
                              n_29=n & 0<=n&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (res=0 & n=0) --> A(res,n),
 (res=0 & n=0) --> A(res,n),
 (exists(n_585:res=1 & n=1 | -1+res=n_585 & -1+n=n_585 & 
  1<=n_585)) --> A(res,n),
 (res=0 & n=0) --> A(res,n),
 (n=1 & res=1) --> A(res,n),
 (n=1 & res=1) --> A(res,n),
 (n=1 & res=1) --> A(res,n),
 (n=1 & res=1) --> A(res,n),
 (n=1 & res=1) --> A(res,n),
 (n=1 & res=1) --> A(res,n),
 (n=1 & res=1) --> A(res,n),
 (n=1 & res=1) --> A(res,n),
 (n=1 & res=1) --> A(res,n),
 (n=1 & res=1) --> A(res,n),
 (n=1 & res=1) --> A(res,n),
 (n=1 & res=1) --> A(res,n),
 (n=1 & res=1) --> A(res,n),
 (n=1 & res=1) --> A(res,n),
 (n=1 & res=1) --> A(res,n),
 (n=1 & res=1) --> A(res,n),
 (n=1 & res=1) --> A(res,n),
 (n=1 & res=1) --> A(res,n),
 (n=1 & res=1) --> A(res,n),
 (n=1 & res=1) --> A(res,n),
 (n=1 & res=1) --> A(res,n),
 (n=1 & res=1) --> A(res,n),
 (n=1 & res=1) --> A(res,n),
 (res=0 & n=0) --> A(res,n),
 (n=1 & res=1) --> A(res,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure count$node SUCCESS

Termination checking result:

Stop Omega... 386 invocations 
0 false contexts at: ()

Total verification time: 0.88 second(s)
	Time spent in main process: 0.61 second(s)
	Time spent in child processes: 0.27 second(s)

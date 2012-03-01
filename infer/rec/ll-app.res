
Processing file "ll-app.ss"
Parsing ll-app.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure append$node~node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ n!=0, n!=0]
!!! REL :  A(z,m,n)
!!! POST:  n>=1 & z>=n & z=m+n
!!! PRE :  1<=n
!!! OLD SPECS: ((None,[]),EInfer [n,A]
              EBase exists (Expl)(Impl)[n; m](ex)x::ll<n>@M[Orig][LHSCase] * 
                    y::ll<m>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::
                                EXISTS(z: x::ll<z>@M[Orig][LHSCase]&A(z,m,n)&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; m](ex)x::ll<n>@M[Orig][LHSCase] * 
                  y::ll<m>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                    EBase true&1<=n & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 1::
                              EXISTS(z_593: x::ll<z_593>@M[Orig][LHSCase]&
                              n>=1 & z_593>=n & z_593=m+n & 0<=n & 0<=m&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (n=1 & z=m+1 & 0<=m) --> A(z,m,n),
 (z_580=z-1 & m=m_558 & n=n_557+1 & 2<=z & 0<=m_558 & 0<=n_557 & 
  A(z_580,m_558,n_557)) --> A(z,m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append$node~node SUCCESS

Termination checking result:

Stop Omega... 100 invocations 
0 false contexts at: ()

Total verification time: 0.1 second(s)
	Time spent in main process: 0.04 second(s)
	Time spent in child processes: 0.06 second(s)

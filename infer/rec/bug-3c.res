
Processing file "bug-3c.ss"
Parsing bug-3c.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure append$node~node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ n!=0 | m!=0, n!=0 | m<=0, n!=0 | m!=0, n!=0 | m<=0]
!!! REL :  A(n,m,z)
!!! POST:  n>=1 & z>=n & z=m+n
!!! PRE :  1<=n & 0<=m
!!! OLD SPECS: ((None,[]),EInfer [n,m,A]
              EBase exists (Expl)(Impl)[n; m](ex)x::ll<n>@M[Orig][LHSCase] * 
                    y::ll<m>@M[Orig][LHSCase]&0<=n & 0<=m&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::
                                EXISTS(z: x::ll<z>@M[Orig][LHSCase]&A(n,m,z)&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; m](ex)x::ll<n>@M[Orig][LHSCase] * 
                  y::ll<m>@M[Orig][LHSCase]&0<=n & 0<=m&{FLOW,(20,21)=__norm}
                    EBase true&1<=n & 0<=m & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 1::
                              EXISTS(z_593: x::ll<z_593>@M[Orig][LHSCase]&
                              n>=1 & z_593>=n & z_593=m+n & 0<=n & 0<=m&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (n=1 & z=m+1 & 0<=m) --> A(n,m,z),
 (z_580=z-1 & n=n_557+1 & m=m_558 & 2<=z & 0<=n_557 & 0<=m_558 & 
  A(n_557,m_558,z_580)) --> A(n,m,z)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append$node~node SUCCESS

Termination checking result:

Stop Omega... 103 invocations 
0 false contexts at: ()

Total verification time: 0.11 second(s)
	Time spent in main process: 0.05 second(s)
	Time spent in child processes: 0.06 second(s)

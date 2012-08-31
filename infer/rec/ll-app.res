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
                    y::ll<m>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}[]
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                              EAssume 64::
                                EXISTS(z: x::ll<z>@M[Orig][LHSCase]&A(z,m,n)&
                                {FLOW,(20,21)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; m](ex)x::ll<n>@M[Orig][LHSCase] * 
                  y::ll<m>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}[]
                    EBase true&1<=n & MayLoop&{FLOW,(1,23)=__flow}[]
                            EAssume 64::
                              EXISTS(z: x::ll<z>@M[Orig][LHSCase]&n>=1 & 
                              z>=n & z=m+n&{FLOW,(20,21)=__norm})[])
!!! NEW RELS:[ (n=1 & z=m+1 & 0<=m) --> A(z,m,n),
 (m_572=m & z_588=z-1 & n=n_571+1 & 2<=z & 0<=m & 0<=n_571 & 
  A(z_588,m_572,n_571)) --> A(z,m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append$node~node SUCCESS

Termination checking result:

Stop Omega... 81 invocations 
0 false contexts at: ()

Total verification time: 0.28 second(s)
	Time spent in main process: 0.22 second(s)
	Time spent in child processes: 0.06 second(s)

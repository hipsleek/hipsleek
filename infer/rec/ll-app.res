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
                    y::ll<m>@M[Orig][LHSCase]&true&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 64::
                                EXISTS(z: x::ll<z>@M[Orig][LHSCase]&A(z,m,n)&
                                {FLOW,(22,23)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; m](ex)x::ll<n>@M[Orig][LHSCase] * 
                  y::ll<m>@M[Orig][LHSCase]&true&{FLOW,(22,23)=__norm}[]
                    EBase emp&1<=n & MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 64::
                              EXISTS(z: x::ll<z>@M[Orig][LHSCase]&n>=1 & 
                              z>=n & z=m+n&{FLOW,(22,23)=__norm})[])
!!! NEW RELS:[ (n=1 & z=m+1 & 0<=m) --> A(z,m,n),
 (m_591=m & z_607=z-1 & n=n_590+1 & 2<=z & 0<=m & 0<=n_590 & 
  A(z_607,m_591,n_590)) --> A(z,m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append$node~node SUCCESS

Termination checking result:

Stop Omega... 78 invocations 
0 false contexts at: ()

Total verification time: 0.28 second(s)
	Time spent in main process: 0.23 second(s)
	Time spent in child processes: 0.05 second(s)

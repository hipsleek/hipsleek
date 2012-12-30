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
                    {FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 64::
                                EXISTS(z: x::ll<z>@M[Orig][LHSCase]&A(n,m,z)&
                                {FLOW,(22,23)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; m](ex)x::ll<n>@M[Orig][LHSCase] * 
                  y::ll<m>@M[Orig][LHSCase]&0<=n & 0<=m&
                  {FLOW,(22,23)=__norm}[]
                    EBase emp&1<=n & 0<=m & MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 64::
                              EXISTS(z: x::ll<z>@M[Orig][LHSCase]&n>=1 & 
                              z>=n & z=m+n&{FLOW,(22,23)=__norm})[])
!!! NEW RELS:[ (n=1 & z=m+1 & 0<=m) --> A(n,m,z),
 (m_591=m & z_607=z-1 & n=n_590+1 & 2<=z & 0<=m & 0<=n_590 & 
  A(n_590,m_591,z_607)) --> A(n,m,z)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append$node~node SUCCESS

Termination checking result:

Stop Omega... 81 invocations 
0 false contexts at: ()

Total verification time: 0.3 second(s)
	Time spent in main process: 0.24 second(s)
	Time spent in child processes: 0.06 second(s)

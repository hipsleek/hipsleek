Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure append$node~node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ n!=0 | m<=0, n!=0 | m!=0, n!=0 | m<=0, n!=0 | m!=0]
!!! REL :  A(n,m,z)
!!! POST:  n>=1 & z>=n & z=m+n
!!! PRE :  true
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
                    EBase emp&(n<=(0-1) | 1<=n | m<=(0-1)) & MayLoop&
                          {FLOW,(1,25)=__flow}[]
                            EAssume 64::
                              EXISTS(z: x::ll<z>@M[Orig][LHSCase]&n>=1 & 
                              z>=n & z=m+n&{FLOW,(22,23)=__norm})[])
!!! NEW RELS:[ (n=1 & z=m+1 & 0<=m) --> A(n,m,z),
 (n=n_589+1 & m=m_590 & z_606=z-1 & 2<=z & 0<=n_589 & 0<=m & 
  A(n_589,m_590,z_606)) --> A(n,m,z)]
!!! NEW ASSUME:[]
Procedure append$node~node SUCCESS

Termination checking result:

Stop Omega... 90 invocations 
0 false contexts at: ()

Total verification time: 0.34 second(s)
	Time spent in main process: 0.27 second(s)
	Time spent in child processes: 0.07 second(s)


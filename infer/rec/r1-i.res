Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure append$node~node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ n!=0, n!=0]
!!! REL :  A(n,m,z)
!!! POST:  n>=1 & z>=n & z=m+n
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [n,A]
              EBase exists (Expl)(Impl)[n; m](ex)x::ll<n>@M[Orig][LHSCase] * 
                    y::ll<m>@M[Orig][LHSCase]&true&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 74::
                                EXISTS(z: x::ll<z>@M[Orig][LHSCase]&A(n,m,z)&
                                {FLOW,(22,23)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; m](ex)x::ll<n>@M[Orig][LHSCase] * 
                  y::ll<m>@M[Orig][LHSCase]&true&{FLOW,(22,23)=__norm}[]
                    EBase emp&(1<=n | n<=(0-1)) & MayLoop&
                          {FLOW,(1,25)=__flow}[]
                            EAssume 74::
                              EXISTS(z: x::ll<z>@M[Orig][LHSCase]&n>=1 & 
                              z>=n & z=m+n&{FLOW,(22,23)=__norm})[])
!!! NEW RELS:[ (n=1 & z=m+1 & 0<=m) --> A(n,m,z),
 (m=m_614 & n=n_613+1 & z_630=z-1 & 0<=n_613 & 2<=z & 0<=m & 
  A(n_613,m_614,z_630)) --> A(n,m,z)]
!!! NEW ASSUME:[]
Procedure append$node~node SUCCESS

Checking procedure foo$node... 
!!! REL :  F(res,n)
!!! POST:  n>=0 & res=0
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [F]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@L[Orig][LHSCase]&true&
                    {FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 72::
                                emp&F(res,n)&{FLOW,(22,23)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@L[Orig][LHSCase]&true&
                  {FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 72::
                              emp&n>=0 & res=0&{FLOW,(22,23)=__norm}[])
!!! NEW RELS:[ (n=0 & res=0) --> F(res,n),
 (n_665=n-1 & 1<=n & F(res,n_665)) --> F(res,n)]
!!! NEW ASSUME:[]
Procedure foo$node SUCCESS

Checking procedure length$node... 
!!! REL :  R(res,n)
!!! POST:  res>=0 & n=res
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [R]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@L[Orig][LHSCase]&true&
                    {FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 69::
                                emp&R(res,n)&{FLOW,(22,23)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@L[Orig][LHSCase]&true&
                  {FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 69::
                              emp&res>=0 & n=res&{FLOW,(22,23)=__norm}[])
!!! NEW RELS:[ (n=0 & res=0) --> R(res,n),
 (res=r_706+1 & n_694=n-1 & 1<=n & R(r_706,n_694)) --> R(res,n)]
!!! NEW ASSUME:[]
Procedure length$node SUCCESS

Termination checking result:

Stop Omega... 118 invocations 
0 false contexts at: ()

Total verification time: 0.39 second(s)
	Time spent in main process: 0.28 second(s)
	Time spent in child processes: 0.11 second(s)



Processing file "r1-i.ss"
Parsing r1-i.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure append$node~node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ n!=0, n!=0]
!!! REL :  A(n,m,z)
!!! POST:  n>=1 & z>=n & z=m+n
!!! PRE :  1<=n
!!! OLD SPECS: ((None,[]),EInfer [n,A]
              EBase exists (Expl)(Impl)[n; m](ex)x::ll<n>@M[Orig][LHSCase] * 
                    y::ll<m>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 6::
                                EXISTS(z: x::ll<z>@M[Orig][LHSCase]&A(n,m,z)&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; m](ex)x::ll<n>@M[Orig][LHSCase] * 
                  y::ll<m>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                    EBase true&1<=n & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 6::
                              EXISTS(z_622: x::ll<z_622>@M[Orig][LHSCase]&
                              n>=1 & z_622>=n & z_622=m+n & 0<=n & 0<=m&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (n=1 & z=m+1 & 0<=m) --> A(n,m,z),
 (z_609=z-1 & m=m_587 & n=n_586+1 & 2<=z & 0<=m_587 & 0<=n_586 & 
  A(n_586,m_587,z_609)) --> A(n,m,z)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append$node~node SUCCESS

Checking procedure foo$node... 
!!! REL :  F(res,n)
!!! POST:  n>=0 & 0=res
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [F]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@L[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 4::
                                true&F(res,n)&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@L[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 4::
                              true&n>=0 & 0=res & 0<=n&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (n=0 & res=0) --> F(res,n),
 (res=m_29' & n_646=n-1 & 1<=n & F(m_29',n_646)) --> F(res,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure foo$node SUCCESS

Checking procedure length$node... 
!!! REL :  R(res,n)
!!! POST:  res>=0 & res=n
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [R]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@L[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::
                                true&R(res,n)&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@L[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 1::
                              true&res>=0 & res=n & 0<=n&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (n=0 & res=0) --> R(res,n),
 (res=r_30'+1 & n_678=n-1 & 1<=n & R(r_30',n_678)) --> R(res,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure length$node SUCCESS

Termination checking result:

Stop Omega... 167 invocations 
0 false contexts at: ()

Total verification time: 0.17 second(s)
	Time spent in main process: 0.06 second(s)
	Time spent in child processes: 0.11 second(s)

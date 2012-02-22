
Processing file "r1-i.ss"
Parsing r1-i.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure append$node~node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ n!=0, n!=0]
!!! REL :  A(n,m,z)
!!! POST:  m>=0 & z>=(1+m) & z=n+m
!!! PRE :  0<=m & 1<=n
!!! OLD SPECS: ((None,[]),EInfer [n,A]
              EBase exists (Expl)(Impl)[n; m](ex)x::ll<n>@M[Orig][LHSCase] * 
                    y::ll<m>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 6::
                                EXISTS(z: x::ll<z>@M[Orig][LHSCase]&A(n,m,z)&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; m](ex)x::ll<n>@M[Orig][LHSCase] * 
                  y::ll<m>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                    EBase true&0<=m & 1<=n & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 6::
                              x::ll<z>@M[Orig][LHSCase]&m>=0 & z>=(1+m) & 
                              z=n+m & 0<=n & 0<=m&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (1+m=z & 1<=z & n=1) --> A(n,m,z),
 (1<=z_609 & 1+n_586=n & m_587=m & -1+z=z_609 & 0<=m & 1<=n & 
  A(n_586,m_587,z_609)) --> A(n,m,z)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append$node~node SUCCESS

Checking procedure foo$node... 
!!! REL :  F(res,n)
!!! POST:  n>=0 & 0=res
!!! PRE :  0<=n
!!! OLD SPECS: ((None,[]),EInfer [F]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@L[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 4::
                                true&F(res,n)&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@L[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&0<=n & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 4::
                              true&n>=0 & 0=res & 0<=n&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (n=0 & res=0) --> F(res,n),
 (exists(flted_7_643:(n_648=0 & n=1 | flted_7_643=n_648 & -1+n=n_648 & 
  1<=n_648) & F(m_29',n_648) & res=m_29')) --> F(res,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure foo$node SUCCESS

Checking procedure length$node... 
!!! REL :  R(res,n)
!!! POST:  res>=0 & res=n
!!! PRE :  0<=n
!!! OLD SPECS: ((None,[]),EInfer [R]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@L[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::
                                true&R(res,n)&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@L[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&0<=n & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 1::
                              true&res>=0 & res=n & 0<=n&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (n=0 & res=0) --> R(res,n),
 (exists(flted_7_678:(n_683=0 & n=1 | flted_7_678=n_683 & -1+n=n_683 & 
  1<=n_683) & R(r_30',n_683) & -1+res=r_30')) --> R(res,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure length$node SUCCESS

Termination checking result:

Stop Omega... 236 invocations 
0 false contexts at: ()

Total verification time: 0.42 second(s)
	Time spent in main process: 0.27 second(s)
	Time spent in child processes: 0.15 second(s)


Processing file "bug-3c.ss"
Parsing bug-3c.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure append$node~node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ n!=0 | m!=0, n!=0 | m<=0, n!=0 | m!=0, n!=0 | m<=0]
!!! REL :  A(n,m,z)
!!! POST:  m>=0 & z>=(1+m) & z=n+m
!!! PRE :  0<=m & 1<=n
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
                    EBase true&0<=m & 1<=n & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 1::
                              x::ll<z>@M[Orig][LHSCase]&m>=0 & z>=(1+m) & 
                              z=n+m & 0<=n & 0<=m&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (1+m=z & 1<=z & n=1) --> A(n,m,z),
 (1<=z_580 & 1+n_557=n & m_558=m & -1+z=z_580 & 1<=n & 0<=m & 
  A(n_557,m_558,z_580)) --> A(n,m,z)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append$node~node SUCCESS

Termination checking result:

Stop Omega... 141 invocations 
0 false contexts at: ()

Total verification time: 0.37 second(s)
	Time spent in main process: 0.26 second(s)
	Time spent in child processes: 0.11 second(s)

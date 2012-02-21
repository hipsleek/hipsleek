
Processing file "ll-app.ss"
Parsing ll-app.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure append$node~node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ n!=0, n!=0]
!!! REL :  A(z,m,n)
!!! POST:  m>=0 & z>=(1+m) & z=n+m
!!! PRE :  0<=m & 1<=n
!!! OLD SPECS: ((None,[]),EInfer [n,A]
              EBase exists (Expl)(Impl)[n; m](ex)x::ll<n>@M[Orig][LHSCase] * 
                    y::ll<m>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::
                                EXISTS(z: x::ll<z>@M[Orig][LHSCase]&A(z,m,n)&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; m](ex)x::ll<n>@M[Orig][LHSCase] * 
                  y::ll<m>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                    EBase true&0<=m & 1<=n & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 1::
                              x::ll<z>@M[Orig][LHSCase]&m>=0 & z>=(1+m) & 
                              z=n+m & 0<=n & 0<=m&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (1+m=z & 1<=z & n=1) --> A(z,m,n),
 (1<=z_580 & 1+n_557=n & m_558=m & -1+z=z_580 & 0<=m & 1<=n & 
  A(z_580,m_558,n_557)) --> A(z,m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append$node~node SUCCESS

Termination checking result:

Stop Omega... 137 invocations 
0 false contexts at: ()

Total verification time: 0.3 second(s)
	Time spent in main process: 0.22 second(s)
	Time spent in child processes: 0.08 second(s)

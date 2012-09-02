Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure append2$node~node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ n1!=0, n1!=0]
!!! OLD SPECS: ((None,[]),EInfer [n1]
              EBase exists (Expl)(Impl)[n1; 
                    n2](ex)x::ll<n1>@M[Orig][LHSCase] * 
                    y::ll<n2>@M[Orig][LHSCase]&true&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 64::
                                EXISTS(m: x::ll<m>@M[Orig][LHSCase]&m=n2+n1&
                                {FLOW,(22,23)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n1; 
                  n2](ex)x::ll<n1>@M[Orig][LHSCase] * 
                  y::ll<n2>@M[Orig][LHSCase]&true&{FLOW,(22,23)=__norm}[]
                    EBase emp&(1<=n1 | n1<=(0-1)) & MayLoop&
                          {FLOW,(1,25)=__flow}[]
                            EAssume 64::
                              EXISTS(m: x::ll<m>@M[Orig][LHSCase]&n2=m-n1 & 
                              1<=n1 & n1<=m&{FLOW,(22,23)=__norm})[])
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append2$node~node SUCCESS

Termination checking result:

Stop Omega... 81 invocations 
0 false contexts at: ()

Total verification time: 0.26 second(s)
	Time spent in main process: 0.23 second(s)
	Time spent in child processes: 0.03 second(s)

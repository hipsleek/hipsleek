Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure delete$node~int... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ n!=1 | a!=1, n!=0 | a!=1, n!=0 | a<=1, n!=0 | 1<=a]
!!! REL :  B(n,a,m)
!!! POST:  a>=1 & m>=a & n=m+1
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [n,a,B]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]&true&
                    {FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 65::
                                EXISTS(m: x::ll<m>@M[Orig][LHSCase]&B(n,a,m)&
                                {FLOW,(22,23)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]&true&
                  {FLOW,(22,23)=__norm}[]
                    EBase emp&(n<=(0-1) | 2<=n | (a<=0 & 1<=n) | (2<=a & 
                          1<=n)) & MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 65::
                              EXISTS(m: x::ll<m>@M[Orig][LHSCase]&a>=1 & 
                              m>=a & n=m+1&{FLOW,(22,23)=__norm})[])
!!! NEW RELS:[ (a=1 & m=n-1 & 2<=n) --> B(n,a,m),
 (((n_633=n-1 & a=v_int_46_651+1 & m=m_650+1 & v_int_46_651<=(0-1) & 
  0<=m_650 & 1<=n) | (n_633=n-1 & a=v_int_46_651+1 & m=m_650+1 & 0<=m_650 & 
  1<=n & 1<=v_int_46_651)) & B(n_633,v_int_46_651,m_650)) --> B(n,a,m)]
!!! NEW ASSUME:[]
Procedure delete$node~int SUCCESS

Termination checking result:

Stop Omega... 97 invocations 
0 false contexts at: ()

Total verification time: 0.35 second(s)
	Time spent in main process: 0.26 second(s)
	Time spent in child processes: 0.09 second(s)


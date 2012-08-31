Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure delete$node~int... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ n!=1 | a!=1, n!=0 | a!=1, n!=0 | a<=1, n!=0 | 1<=a]
!!! REL :  B(n,a,m)
!!! POST:  a>=1 & m>=a & m+1=n
!!! PRE :  1<=a & a<n
!!! OLD SPECS: ((None,[]),EInfer [n,a,B]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}[]
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                              EAssume 65::
                                EXISTS(m: x::ll<m>@M[Orig][LHSCase]&B(n,a,m)&
                                {FLOW,(20,21)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}[]
                    EBase true&1<=a & a<n & MayLoop&{FLOW,(1,23)=__flow}[]
                            EAssume 65::
                              EXISTS(m: x::ll<m>@M[Orig][LHSCase]&a>=1 & 
                              m>=a & m+1=n&{FLOW,(20,21)=__norm})[])
!!! NEW RELS:[ (a=1 & m=n-1 & 2<=n) --> B(n,a,m),
 ((n_615=n-1 & v_int_46_633=a-1 & m=m_632+1 & 1<=n & 0<=m_632 & 2<=a | 
  n_615=n-1 & v_int_46_633=a-1 & m=m_632+1 & a<=0 & 1<=n & 0<=m_632) & 
  B(n_615,v_int_46_633,m_632)) --> B(n,a,m)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete$node~int SUCCESS

Termination checking result:

Stop Omega... 96 invocations 
0 false contexts at: ()

Total verification time: 0.31 second(s)
	Time spent in main process: 0.23 second(s)
	Time spent in child processes: 0.08 second(s)

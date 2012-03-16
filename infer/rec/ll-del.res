
Processing file "ll-del.ss"
Parsing ll-del.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
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
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::
                                EXISTS(m: x::ll<m>@M[Orig][LHSCase]&B(n,a,m)&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&1<=a & a<n & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 1::
                              EXISTS(m_636: x::ll<m_636>@M[Orig][LHSCase]&
                              a>=1 & m_636>=a & m_636+1=n & 0<=n&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (a=1 & m=n-1 & 2<=n) --> B(n,a,m),
 ((n_601=n-1 & m=m_622+1 & a=v_int_46_623+1 & 1<=n & 0<=m_622 & 
  1<=v_int_46_623 | n_601=n-1 & m=m_622+1 & a=v_int_46_623+1 & 
  v_int_46_623<=(0-1) & 1<=n & 0<=m_622) & 
  B(n_601,v_int_46_623,m_622)) --> B(n,a,m)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete$node~int SUCCESS

Termination checking result:

Stop Omega... 112 invocations 
0 false contexts at: ()

Total verification time: 0.13 second(s)
	Time spent in main process: 0.05 second(s)
	Time spent in child processes: 0.08 second(s)

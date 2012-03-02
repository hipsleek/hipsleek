
Processing file "dll-insert.ss"
Parsing dll-insert.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure insert$node2~int... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null, x!=null]
!!! REL :  A(m,n)
!!! POST:  n>=1 & n+1=m
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [x,A]
              EBase exists (Expl)(Impl)[p; 
                    n](ex)x::dll<p,n>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::
                                EXISTS(p_25,
                                m: x::dll<p_25,m>@M[Orig][LHSCase]&A(m,n) & 
                                p_25=p&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p; n](ex)x::dll<p,n>@M[Orig][LHSCase]&
                  true&{FLOW,(20,21)=__norm}
                    EBase true&x!=null & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 1::
                              EXISTS(p_660,
                              m_661: x::dll<p_660,m_661>@M[Orig][LHSCase]&
                              p_660=p & n>=1 & n+1=m_661 & 0<=n&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (n=1 & m=2) --> A(m,n),
 (m_635=m-1 & n=n_588+1 & 2<=m & 0<=n_588 & A(m_635,n_588)) --> A(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert$node2~int SUCCESS

Termination checking result:

Stop Omega... 93 invocations 
0 false contexts at: ()

Total verification time: 0.09 second(s)
	Time spent in main process: 0.05 second(s)
	Time spent in child processes: 0.04 second(s)

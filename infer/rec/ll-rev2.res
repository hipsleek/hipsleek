
Processing file "ll-rev2.ss"
Parsing ll-rev2.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure reverse$node~node... 
!!! REL :  A(xs',m,n,t)
!!! POST:  m>=0 & t>=m & xs'=null & t=n+m
!!! PRE :  0<=m & 0<=n
!!! OLD SPECS: ((None,[]),EInfer [A]
              EBase exists (Expl)(Impl)[n; 
                    m](ex)xs::ll<n>@M[Orig][LHSCase] * 
                    ys::ll<m>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::ref [xs;ys]
                                EXISTS(t: ys'::ll<t>@M[Orig][LHSCase]&
                                A(xs',m,n,t)&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; m](ex)xs::ll<n>@M[Orig][LHSCase] * 
                  ys::ll<m>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                    EBase true&0<=m & 0<=n & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 1::ref [xs;ys]
                              ys'::ll<t>@M[Orig][LHSCase]&m>=0 & t>=m & 
                              xs'=null & t=n+m & 0<=n & 0<=m&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(xs:t=t_573 & 0<=t_573 & A(xs',m_551,n_550,t_573) & 1<=n & 0<=m & 
  xs!=null & -1+m_551=m & 1+n_550=n)) --> A(xs',m,n,t),
 (t=m & 0<=m & n=0 & xs'=null) --> A(xs',m,n,t)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure reverse$node~node SUCCESS

Termination checking result:

Stop Omega... 97 invocations 
0 false contexts at: ()

Total verification time: 0.26 second(s)
	Time spent in main process: 0.2 second(s)
	Time spent in child processes: 0.06 second(s)

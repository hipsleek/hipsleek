Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure reverse$node~node... 
!!! REL :  A(m,n,t)
!!! POST:  n>=0 & t>=n & t=m+n
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [A]
              EBase exists (Expl)(Impl)[n; 
                    m](ex)xs::ll<n>@M[Orig][LHSCase] * 
                    ys::ll<m>@M[Orig][LHSCase]&true&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 67::ref [xs;ys]
                                EXISTS(t: ys'::ll<t>@M[Orig][LHSCase]&
                                xs'=null & A(m,n,t)&{FLOW,(22,23)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; m](ex)xs::ll<n>@M[Orig][LHSCase] * 
                  ys::ll<m>@M[Orig][LHSCase]&true&{FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 67::ref [xs;ys]
                              EXISTS(t: ys'::ll<t>@M[Orig][LHSCase]&
                              xs'=null & n>=0 & t>=n & t=m+n&
                              {FLOW,(22,23)=__norm})[])
!!! NEW RELS:[ (n_584=n-1 & m=m_585-1 & t_603=t & 1<=n & 1<=m_585 & 0<=t & 
  A(m_585,n_584,t_603)) --> A(m,n,t),
 (n=0 & m=t & 0<=t) --> A(m,n,t)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure reverse$node~node SUCCESS

Termination checking result:

Stop Omega... 73 invocations 
0 false contexts at: ()

Total verification time: 0.28 second(s)
	Time spent in main process: 0.22 second(s)
	Time spent in child processes: 0.06 second(s)

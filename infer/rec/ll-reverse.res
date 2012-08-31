Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure reverse$node~node... 
!!! REL :  A(m,n,t)
!!! POST:  n>=0 & t>=n & t=m+n
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [A]
              EBase exists (Expl)(Impl)[n; 
                    m](ex)xs::ll<n>@M[Orig][LHSCase] * 
                    ys::ll<m>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}[]
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                              EAssume 67::ref [xs;ys]
                                EXISTS(t: ys'::ll<t>@M[Orig][LHSCase]&
                                xs'=null & A(m,n,t)&{FLOW,(20,21)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; m](ex)xs::ll<n>@M[Orig][LHSCase] * 
                  ys::ll<m>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}[]
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                            EAssume 67::ref [xs;ys]
                              EXISTS(t: ys'::ll<t>@M[Orig][LHSCase]&
                              xs'=null & n>=0 & t>=n & t=m+n&
                              {FLOW,(20,21)=__norm})[])
!!! NEW RELS:[ (n_564=n-1 & m=m_565-1 & t_583=t & 1<=n & 1<=m_565 & 0<=t & 
  A(m_565,n_564,t_583)) --> A(m,n,t),
 (n=0 & m=t & 0<=t) --> A(m,n,t)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure reverse$node~node SUCCESS

Termination checking result:

Stop Omega... 76 invocations 
0 false contexts at: ()

Total verification time: 0.27 second(s)
	Time spent in main process: 0.21 second(s)
	Time spent in child processes: 0.06 second(s)


Processing file "ll-reverse.ss"
Parsing ll-reverse.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure reverse$node~node... 
!!! REL :  A(m,n,t)
!!! POST:  n>=0 & t>=n & t=m+n
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [A]
              EBase exists (Expl)(Impl)[n; 
                    m](ex)xs::ll<n>@M[Orig][LHSCase] * 
                    ys::ll<m>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::ref [xs;ys]
                                EXISTS(t: ys'::ll<t>@M[Orig][LHSCase]&
                                xs'=null & A(m,n,t)&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; m](ex)xs::ll<n>@M[Orig][LHSCase] * 
                  ys::ll<m>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 1::ref [xs;ys]
                              EXISTS(t_579: ys'::ll<t_579>@M[Orig][LHSCase]&
                              xs'=null & n>=0 & t_579>=n & t_579=m+n & 
                              0<=n & 0<=m&{FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (n_550=n-1 & m_551=m+1 & t_573=t & 1<=n & 0<=m & 0<=t & 
  A(m_551,n_550,t_573)) --> A(m,n,t),
 (n=0 & m=t & 0<=t) --> A(m,n,t)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure reverse$node~node SUCCESS

Termination checking result:

Stop Omega... 101 invocations 
0 false contexts at: ()

Total verification time: 0.1 second(s)
	Time spent in main process: 0.04 second(s)
	Time spent in child processes: 0.06 second(s)

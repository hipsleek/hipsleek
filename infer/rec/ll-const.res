
Processing file "ll-const.ss"
Parsing ll-const.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure foo$node... 
!!! REL :  F(res,n)
!!! POST:  n>=0 & 0=res
!!! PRE :  0<=n
!!! OLD SPECS: ((None,[]),EInfer [F]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@L[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::
                                true&F(res,n)&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@L[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&0<=n & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 1::
                              true&n>=0 & 0=res & 0<=n&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (n=0 & res=0) --> F(res,n),
 (exists(flted_7_533:(n_538=0 & n=1 | flted_7_533=n_538 & -1+n=n_538 & 
  1<=n_538) & F(m_24',n_538) & res=m_24')) --> F(res,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure foo$node SUCCESS

Termination checking result:

Stop Omega... 90 invocations 
0 false contexts at: ()

Total verification time: 0.23 second(s)
	Time spent in main process: 0.17 second(s)
	Time spent in child processes: 0.06 second(s)

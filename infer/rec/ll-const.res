
Processing file "ll-const.ss"
Parsing ll-const.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure foo$node... 
!!! REL :  F(res,n)
!!! POST:  n>=0 & 0=res
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [F]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@L[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::
                                true&F(res,n)&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@L[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 1::
                              true&n>=0 & 0=res & 0<=n&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (n=0 & res=0) --> F(res,n),
 (res=m_24' & n_538=n-1 & 1<=n & F(m_24',n_538)) --> F(res,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure foo$node SUCCESS

Termination checking result:

Stop Omega... 73 invocations 
0 false contexts at: ()

Total verification time: 0.08 second(s)
	Time spent in main process: 0.04 second(s)
	Time spent in child processes: 0.04 second(s)

Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure bubble$node... 
!!! REL :  A(res)
!!! POST:  !(res)
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [A]
              EBase exists (Expl)(Impl)[n](ex)xs::ll<n>@M[Orig][LHSCase]&
                    xs!=null&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 70::
                                
                                EXISTS(n_36,s,
                                l: xs::sll<n_36,s,l>@M[Orig][LHSCase]&
                                A(res) & n_36=n&{FLOW,(22,23)=__norm})[]
                                or EXISTS(n_37: xs::ll<n_37>@M[Orig][LHSCase]&
                                   res & n_37=n&{FLOW,(22,23)=__norm})[]
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)xs::ll<n>@M[Orig][LHSCase]&
                  xs!=null&{FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 70::
                              
                              EXISTS(n_36,s,
                              l: xs::sll<n_36,s,l>@M[Orig][LHSCase]&n_36=n & 
                              !(res)&{FLOW,(22,23)=__norm})[]
                              or EXISTS(n_37: xs::ll<n_37>@M[Orig][LHSCase]&
                                 res & n_37=n&{FLOW,(22,23)=__norm})[]
                              )
!!! NEW RELS:[ (1<=res & tmp_985 & A(tmp_985)) --> A(res),
 (res<=0) --> A(res),
 (res<=0 & !(tmp_1079) & A(tmp_1079)) --> A(res)]
!!! NEW ASSUME:[ RELASS [A]: ( A(tmp_841)) -->  !(tmp_841),
 RELASS [A]: ( A(tmp_913)) -->  tmp_913]
!!! NEW RANK:[]
Procedure bubble$node SUCCESS

Termination checking result:

Stop Omega... 217 invocations 
0 false contexts at: ()

Total verification time: 1.08 second(s)
	Time spent in main process: 0.99 second(s)
	Time spent in child processes: 0.09 second(s)

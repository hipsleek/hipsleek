Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure bubble$node... 
!!! REL :  A(res)
!!! POST:  !(res)
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [A]
              EBase exists (Expl)(Impl)[n](ex)xs::ll<n>@M[Orig][LHSCase]&
                    xs!=null&{FLOW,(20,21)=__norm}[]
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                              EAssume 70::
                                
                                EXISTS(n_40,s,
                                l: xs::sll<n_40,s,l>@M[Orig][LHSCase]&
                                A(res) & n_40=n&{FLOW,(20,21)=__norm})[]
                                or EXISTS(n_41: xs::ll<n_41>@M[Orig][LHSCase]&
                                   res & n_41=n&{FLOW,(20,21)=__norm})[]
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)xs::ll<n>@M[Orig][LHSCase]&
                  xs!=null&{FLOW,(20,21)=__norm}[]
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                            EAssume 70::
                              
                              EXISTS(n_40,s,
                              l: xs::sll<n_40,s,l>@M[Orig][LHSCase]&n_40=n & 
                              !(res)&{FLOW,(20,21)=__norm})[]
                              or EXISTS(n_41: xs::ll<n_41>@M[Orig][LHSCase]&
                                 res & n_41=n&{FLOW,(20,21)=__norm})[]
                              )
!!! NEW RELS:[ (1<=res & tmp_44' & A(tmp_44')) --> A(res),
 (res<=0) --> A(res),
 (res<=0 & !(tmp_44') & A(tmp_44')) --> A(res)]
!!! NEW ASSUME:[ RELASS [A]: ( A(tmp_44')) -->  !(tmp_44'),
 RELASS [A]: ( A(tmp_44')) -->  tmp_44']
!!! NEW RANK:[]
Procedure bubble$node SUCCESS

Termination checking result:

Stop Omega... 223 invocations 
0 false contexts at: ()

Total verification time: 1.07 second(s)
	Time spent in main process: 0.98 second(s)
	Time spent in child processes: 0.09 second(s)

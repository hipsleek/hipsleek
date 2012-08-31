Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure bubble$node... 
!!! REL :  B(res)
!!! POST:  res
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [B]
              EBase exists (Expl)(Impl)[n](ex)xs::ll<n>@M[Orig][LHSCase]&
                    xs!=null&{FLOW,(20,21)=__norm}[]
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                              EAssume 70::
                                
                                EXISTS(n_40,s,
                                l: xs::sll<n_40,s,l>@M[Orig][LHSCase]&
                                !(res) & n_40=n&{FLOW,(20,21)=__norm})[]
                                or EXISTS(n_41: xs::ll<n_41>@M[Orig][LHSCase]&
                                   B(res) & n_41=n&{FLOW,(20,21)=__norm})[]
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)xs::ll<n>@M[Orig][LHSCase]&
                  xs!=null&{FLOW,(20,21)=__norm}[]
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                            EAssume 70::
                              
                              EXISTS(n_40,s,
                              l: xs::sll<n_40,s,l>@M[Orig][LHSCase]&!(res) & 
                              n_40=n&{FLOW,(20,21)=__norm})[]
                              or EXISTS(n_41: xs::ll<n_41>@M[Orig][LHSCase]&
                                 n_41=n & res&{FLOW,(20,21)=__norm})[]
                              )
!!! NEW RELS:[ (res<=0) --> B(res),
 (1<=res & tmp_44' & B(tmp_44')) --> B(res),
 (res<=0 & !(tmp_44') & B(tmp_44')) --> B(res),
 (1<=res) --> B(res)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure bubble$node SUCCESS

Termination checking result:

Stop Omega... 222 invocations 
0 false contexts at: ()

Total verification time: 0.94 second(s)
	Time spent in main process: 0.85 second(s)
	Time spent in child processes: 0.09 second(s)

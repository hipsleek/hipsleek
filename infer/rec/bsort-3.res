Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure bubble$node... 
!!! REL :  B(res)
!!! POST:  res
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [B]
              EBase exists (Expl)(Impl)[n](ex)xs::ll<n>@M[Orig][LHSCase]&
                    xs!=null&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 70::
                                
                                EXISTS(n_36,s,
                                l: xs::sll<n_36,s,l>@M[Orig][LHSCase]&
                                !(res) & n_36=n&{FLOW,(22,23)=__norm})[]
                                or EXISTS(n_37: xs::ll<n_37>@M[Orig][LHSCase]&
                                   B(res) & n_37=n&{FLOW,(22,23)=__norm})[]
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)xs::ll<n>@M[Orig][LHSCase]&
                  xs!=null&{FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 70::
                              
                              EXISTS(n_36,s,
                              l: xs::sll<n_36,s,l>@M[Orig][LHSCase]&!(res) & 
                              n_36=n&{FLOW,(22,23)=__norm})[]
                              or EXISTS(n_37: xs::ll<n_37>@M[Orig][LHSCase]&
                                 n_37=n & res&{FLOW,(22,23)=__norm})[]
                              )
!!! NEW RELS:[ (res<=0) --> B(res),
 (1<=res & tmp_1053 & B(tmp_1053)) --> B(res),
 (res<=0 & !(tmp_1123) & B(tmp_1123)) --> B(res),
 (1<=res) --> B(res)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure bubble$node SUCCESS

Termination checking result:

Stop Omega... 213 invocations 
0 false contexts at: ()

Total verification time: 0.96 second(s)
	Time spent in main process: 0.87 second(s)
	Time spent in child processes: 0.09 second(s)

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
                                
                                EXISTS(n_42,s,
                                l: xs::sll<n_42,s,l>@M[Orig][LHSCase]&
                                !(res) & n=n_42&{FLOW,(22,23)=__norm})[]
                                or EXISTS(n_43: xs::ll<n_43>@M[Orig][LHSCase]&
                                   B(res) & n=n_43&{FLOW,(22,23)=__norm})[]
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)xs::ll<n>@M[Orig][LHSCase]&
                  xs!=null&{FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 70::
                              
                              EXISTS(n_42,s,
                              l: xs::sll<n_42,s,l>@M[Orig][LHSCase]&!(res) & 
                              n=n_42&{FLOW,(22,23)=__norm})[]
                              or EXISTS(n_43: xs::ll<n_43>@M[Orig][LHSCase]&
                                 n=n_43 & res&{FLOW,(22,23)=__norm})[]
                              )
!!! NEW RELS:[ (res<=0) --> B(res),
 (tmp_1050 & 1<=res & B(tmp_1050)) --> B(res),
 (!(tmp_1120) & res<=0 & B(tmp_1120)) --> B(res),
 (1<=res) --> B(res)]
!!! NEW ASSUME:[]
Procedure bubble$node SUCCESS

Termination checking result:

Stop Omega... 308 invocations 
0 false contexts at: ()

Total verification time: 1.15 second(s)
	Time spent in main process: 0.78 second(s)
	Time spent in child processes: 0.37 second(s)


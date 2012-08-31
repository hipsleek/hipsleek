Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure bubble$node... 
!!! REL :  A(res)
!!! POST:  !(res)
!!! PRE :  true
!!! REL :  B(res)
!!! POST:  true
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [xs,A,B]
              EBase exists (Expl)(Impl)[n](ex)xs::ll<n>@M[Orig][LHSCase]&
                    xs!=null&{FLOW,(20,21)=__norm}[]
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                              EAssume 70::
                                
                                EXISTS(n_40,s,
                                l: xs::sll<n_40,s,l>@M[Orig][LHSCase]&
                                A(res) & n_40=n&{FLOW,(20,21)=__norm})[]
                                or EXISTS(n_41: xs::ll<n_41>@M[Orig][LHSCase]&
                                   B(res) & n_41=n&{FLOW,(20,21)=__norm})[]
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)xs::ll<n>@M[Orig][LHSCase]&
                  xs!=null&{FLOW,(20,21)=__norm}[]
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                            EAssume 70::
                              
                              EXISTS(n_40,s,
                              l: xs::sll<n_40,s,l>@M[Orig][LHSCase]&n_40=n & 
                              !(res)&{FLOW,(20,21)=__norm})[]
                              or EXISTS(n_41: xs::ll<n_41>@M[Orig][LHSCase]&
                                 n_41=n&{FLOW,(20,21)=__norm})[]
                              )
!!! NEW RELS:[ (res<=0) --> A(res),
 (tmp_44' & 1<=res & A(tmp_44')) --> A(res),
 (!(tmp_44') & res<=0 & A(tmp_44')) --> A(res),
 (1<=res & tmp_44' & A(tmp_44')) --> A(res),
 (res<=0 & !(tmp_44') & A(tmp_44')) --> A(res),
 (res<=0) --> B(res),
 (1<=res & A(tmp_44')) --> B(res),
 (res<=0 & A(tmp_44')) --> B(res),
 (1<=res & tmp_44' & B(tmp_44')) --> B(res),
 (res<=0 & !(tmp_44') & B(tmp_44')) --> B(res)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure bubble$node SUCCESS

Termination checking result:

Stop Omega... 350 invocations 
0 false contexts at: ()

Total verification time: 1.58 second(s)
	Time spent in main process: 1.18 second(s)
	Time spent in child processes: 0.4 second(s)

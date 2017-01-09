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
                    xs!=null&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 70::
                                
                                EXISTS(n_36,s,
                                l: xs::sll<n_36,s,l>@M[Orig][LHSCase]&
                                A(res) & n_36=n&{FLOW,(22,23)=__norm})[]
                                or EXISTS(n_37: xs::ll<n_37>@M[Orig][LHSCase]&
                                   B(res) & n_37=n&{FLOW,(22,23)=__norm})[]
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)xs::ll<n>@M[Orig][LHSCase]&
                  xs!=null&{FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 70::
                              
                              EXISTS(n_36,s,
                              l: xs::sll<n_36,s,l>@M[Orig][LHSCase]&n_36=n & 
                              !(res)&{FLOW,(22,23)=__norm})[]
                              or EXISTS(n_37: xs::ll<n_37>@M[Orig][LHSCase]&
                                 n_37=n&{FLOW,(22,23)=__norm})[]
                              )
!!! NEW RELS:[ (res<=0) --> A(res),
 (tmp_844 & 1<=res & A(tmp_844)) --> A(res),
 (!(tmp_918) & res<=0 & A(tmp_918)) --> A(res),
 (1<=res & tmp_992 & A(tmp_992)) --> A(res),
 (res<=0 & !(tmp_1087) & A(tmp_1087)) --> A(res),
 (res<=0) --> B(res),
 (1<=res & A(tmp_897)) --> B(res),
 (res<=0 & A(tmp_971)) --> B(res),
 (1<=res & A(tmp_1053)) --> B(res),
 (res<=0 & A(tmp_1148)) --> B(res),
 (1<=res & tmp_1232 & B(tmp_1232)) --> B(res),
 (res<=0 & !(tmp_1302) & B(tmp_1302)) --> B(res)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure bubble$node SUCCESS

Termination checking result:

Stop Omega... 338 invocations 
0 false contexts at: ()

Total verification time: 1.52 second(s)
	Time spent in main process: 1.2 second(s)
	Time spent in child processes: 0.32 second(s)

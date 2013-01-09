Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure bubble$node... 
!!! REL :  B(res)
!!! POST:  true
!!! PRE :  true
!!! REL :  A(res)
!!! POST:  true
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [xs,A,B]
              EBase exists (Expl)(Impl)[n](ex)xs::ll<n>@M[Orig][LHSCase]&
                    xs!=null&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 70::
                                
                                EXISTS(n_42,s,
                                l: xs::sll<n_42,s,l>@M[Orig][LHSCase]&
                                A(res) & n=n_42&{FLOW,(22,23)=__norm})[]
                                or EXISTS(n_43: xs::ll<n_43>@M[Orig][LHSCase]&
                                   B(res) & n=n_43&{FLOW,(22,23)=__norm})[]
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)xs::ll<n>@M[Orig][LHSCase]&
                  xs!=null&{FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 70::
                              
                              EXISTS(n_42,s,
                              l: xs::sll<n_42,s,l>@M[Orig][LHSCase]&n=n_42&
                              {FLOW,(22,23)=__norm})[]
                              or EXISTS(n_43: xs::ll<n_43>@M[Orig][LHSCase]&
                                 n=n_43&{FLOW,(22,23)=__norm})[]
                              )
!!! NEW RELS:[ (res<=0) --> A(res),
 (tmp_841 & 1<=res & A(tmp_841)) --> A(res),
 (!(tmp_915) & res<=0 & A(tmp_915)) --> A(res),
 (tmp_989 & 1<=res & A(tmp_989)) --> A(res),
 (!(tmp_1084) & res<=0 & A(tmp_1084)) --> A(res),
 (1<=res) --> A(res),
 (res<=0) --> B(res),
 (tmp_894 & 1<=res & A(tmp_894)) --> B(res),
 (!(tmp_968) & res<=0 & A(tmp_968)) --> B(res),
 (tmp_1050 & 1<=res & A(tmp_1050)) --> B(res),
 (!(tmp_1145) & res<=0 & A(tmp_1145)) --> B(res),
 (tmp_1229 & 1<=res & B(tmp_1229)) --> B(res),
 (!(tmp_1299) & res<=0 & B(tmp_1299)) --> B(res),
 (1<=res & A(tmp_1372)) --> B(res),
 (1<=res & A(tmp_1453)) --> B(res),
 (1<=res) --> B(res)]
!!! NEW ASSUME:[]
Procedure bubble$node SUCCESS

Termination checking result:

Stop Omega... 482 invocations 
0 false contexts at: ()

Total verification time: 2.25 second(s)
	Time spent in main process: 1.15 second(s)
	Time spent in child processes: 1.1 second(s)


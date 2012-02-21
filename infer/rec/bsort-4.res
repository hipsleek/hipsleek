
Processing file "bsort-4.ss"
Parsing bsort-4.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure bubble$node... 
!!! REL :  A(res)
!!! POST:  !(res)
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [A]
              EBase exists (Expl)(Impl)[n](ex)xs::ll<n>@M[Orig][LHSCase]&
                    xs!=null&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::
                                
                                EXISTS(n_38,s,
                                l: xs::sll<n_38,s,l>@M[Orig][LHSCase]&
                                A(res) & n_38=n&{FLOW,(20,21)=__norm})
                                or EXISTS(n_39: xs::ll<n_39>@M[Orig][LHSCase]&
                                   res & n_39=n&{FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)xs::ll<n>@M[Orig][LHSCase]&
                  xs!=null&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 1::
                              
                              xs::sll<n_38,s,l>@M[Orig][LHSCase]&n_38=n & 
                              !(res) & 0<=n&{FLOW,(20,21)=__norm}
                              or xs::ll<n_39>@M[Orig][LHSCase]&res & 
                                 n_39=n & 0<=n&{FLOW,(20,21)=__norm}
                              )
!!! NEW RELS:[ (tmp_42' & 1<=res & A(tmp_42')) --> A(res),
 (A(tmp_42') & 1<=res & tmp_42') --> A(res),
 (res<=0) --> A(res),
 (!(tmp_42') & res<=0 & A(tmp_42')) --> A(res),
 (A(tmp_42') & res<=0 & !(tmp_42')) --> A(res)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure bubble$node SUCCESS

Termination checking result:

Stop Omega... 742 invocations 
0 false contexts at: ()

Total verification time: 2.68 second(s)
	Time spent in main process: 1.86 second(s)
	Time spent in child processes: 0.82 second(s)

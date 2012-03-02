
Processing file "bsort-3.ss"
Parsing bsort-3.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure bubble$node... 
!!! REL :  B(res)
!!! POST:  res
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [B]
              EBase exists (Expl)(Impl)[n](ex)xs::ll<n>@M[Orig][LHSCase]&
                    xs!=null&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::
                                
                                EXISTS(n_38,s,
                                l: xs::sll<n_38,s,l>@M[Orig][LHSCase]&
                                !(res) & n_38=n&{FLOW,(20,21)=__norm})
                                or EXISTS(n_39: xs::ll<n_39>@M[Orig][LHSCase]&
                                   B(res) & n_39=n&{FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)xs::ll<n>@M[Orig][LHSCase]&
                  xs!=null&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 1::
                              
                              EXISTS(n_1301,s_1302,
                              l_1303: xs::sll<n_1301,s_1302,l_1303>@M[Orig][LHSCase]&
                              !(res) & n_1301=n & 0<=n&{FLOW,(20,21)=__norm})
                              or EXISTS(n_1304: xs::ll<n_1304>@M[Orig][LHSCase]&
                                 n_1304=n & res & 0<=n&{FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[ (res<=0) --> B(res),
 (1<=res & tmp_42' & B(tmp_42')) --> B(res),
 (res<=0 & !(tmp_42') & B(tmp_42')) --> B(res),
 (1<=res) --> B(res)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure bubble$node SUCCESS

Termination checking result:

Stop Omega... 240 invocations 
0 false contexts at: ()

Total verification time: 0.23 second(s)
	Time spent in main process: 0.15 second(s)
	Time spent in child processes: 0.08 second(s)

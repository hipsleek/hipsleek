/usr/local/bin/mona

Processing file "ll-insert.ss"
Parsing ll-insert.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Translating global variables to procedure parameters...

Checking procedure insert$node~int... Starting Omega...oc

!!! REL :  A(S,S1,a)
!!! POST:  S1=union(S,{a})
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [A]
              EBase exists (Expl)(Impl)[S](ex)x::ll<S>@M[Orig][LHSCase]&
                    S!=()&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::
                                EXISTS(S1: x::ll<S1>@M[Orig][LHSCase]&
                                A(S,S1,a)&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[S](ex)x::ll<S>@M[Orig][LHSCase]&S!=()&
                  {FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 1::
                              EXISTS(S1_621: x::ll<S1_621>@M[Orig][LHSCase]&
                              S1_621=union(S,{a})&{FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_590:exists(v_588:exists(S1_550:exists(v_548:exists(S1_583:exists(v_581:S1_590= & 
  S1_590= & S1_583=union(S1_590,{v_588}) & S1_583=union(S1_590,{v_588}) & 
  S1_550= & v_548=v_581 & a=v_588 & S=union(S1_550,{v_548}) & S!=() & 
  S1=union(S1_583,{v_581})))))))) --> A(S,S1,a),
 (exists(S1_616:exists(v_615:exists(S1_550:exists(v_548:exists(S1_603:exists(v_601:S1_600=union(S1_616,
  {v_615}) & S1_600=S1_603 & v_548=v_601 & S1_550=S_565 & 
  A(S_565,S1_600,a) & S=union(S1_550,{v_548}) & S!=() & S1=union(S1_603,
  {v_601})))))))) --> A(S,S1,a)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert$node~int SUCCESS

Termination checking result:


0 false contexts at: ()

Total verification time: 0.16 second(s)
	Time spent in main process: 0.05 second(s)
	Time spent in child processes: 0.11 second(s)

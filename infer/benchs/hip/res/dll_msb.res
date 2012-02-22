/usr/local/bin/mona

Processing file "dll_msb.ss"
Parsing dll_msb.ss ...
Parsing ../../../prelude.ss ...
Starting Reduce... 
Translating global variables to procedure parameters...

Checking procedure append$node2~node2... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...
Starting Omega...oc

!!! REL :  APP(S,S1,S2)
!!! POST:  S=union(S1,S2)
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [APP]
              EBase exists (Expl)(Impl)[q; m; S1; p; n; 
                    S2](ex)x::dll<q,m,S1>@M[Orig][LHSCase] * 
                    y::dll<p,n,S2>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 12::
                                EXISTS(Anon_12,t,
                                S: res::dll<Anon_12,t,S>@M[Orig][LHSCase]&
                                t=n+m & APP(S,S1,S2)&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[q; m; S1; p; n; 
                  S2](ex)x::dll<q,m,S1>@M[Orig][LHSCase] * 
                  y::dll<p,n,S2>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 12::
                              res::dll<Anon_12,t,S>@M[Orig][LHSCase]&t=n+m & 
                              S=union(S1,S2) & 0<=m & 0<=n&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(S1_1055:exists(v_1054:(S2= | S2=union(S1_1055,{v_1054})) & S1= & 
  S2=S))) --> APP(S,S1,S2),
 (exists(S1_1199:exists(v_1198:exists(S1_833:exists(v_831:exists(v_1071:exists(S1_1073:exists(S1_1010:exists(S1_1096:exists(v_1008:exists(v_1094:(S1_1010= | 
  S1_1010=union(S1_1199,{v_1198})) & S=union(S1_1073,{v_1071}) & 
  S1=union(S1_833,{v_831}) & APP(S_938,S1_841,S2_844) & S2=S2_844 & 
  S1_833=S1_841 & v_831=v_1071 & S_938=union(S1_1010,{v_1008}) & 
  S1_1073=union(S1_1096,{v_1094}) & S1_1073=union(S1_1096,{v_1094}) & 
  S1_1010=S1_1096 & v_1008=v_1094))))))))))) --> APP(S,S1,S2),
 (exists(S1_833:exists(v_831:exists(S1_1221:exists(v_1219:S1_1221= & 
  S1_1221= & S_920= & v_831=v_1219 & S1_833=S1_841 & S2=S2_844 & 
  APP(S_920,S1_841,S2_844) & S1=union(S1_833,{v_831}) & S=union(S1_1221,
  {v_1219})))))) --> APP(S,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append$node2~node2 SUCCESS

Checking procedure append0$node2~node2... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  APP(S,S1,S2)
!!! POST:  S=union(S1,S2)
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [APP]
              EBase exists (Expl)(Impl)[q; S1; p; 
                    S2](ex)x::dll2<q,S1>@M[Orig][LHSCase] * 
                    y::dll2<p,S2>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 4::
                                EXISTS(Anon_11,
                                S: res::dll2<Anon_11,S>@M[Orig][LHSCase]&
                                APP(S,S1,S2)&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[q; S1; p; 
                  S2](ex)x::dll2<q,S1>@M[Orig][LHSCase] * 
                  y::dll2<p,S2>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 4::
                              res::dll2<Anon_11,S>@M[Orig][LHSCase]&
                              S=union(S1,S2)&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(S1_1516:exists(v_1515:(S2= | S2=union(S1_1516,{v_1515})) & S1= & 
  S2=S))) --> APP(S,S1,S2),
 (exists(S1_1561:exists(v_1560:exists(S1_1409:exists(v_1407:exists(v_1519:exists(S1_1521:exists(S1_1492:exists(S1_1534:exists(v_1490:exists(v_1532:(S1_1492= | 
  S1_1492=union(S1_1561,{v_1560})) & S=union(S1_1521,{v_1519}) & 
  S1=union(S1_1409,{v_1407}) & APP(S_1457,S1_1414,S2_1416) & S2=S2_1416 & 
  S1_1409=S1_1414 & v_1407=v_1519 & S_1457=union(S1_1492,{v_1490}) & 
  S1_1521=union(S1_1534,{v_1532}) & S1_1521=union(S1_1534,{v_1532}) & 
  S1_1492=S1_1534 & v_1490=v_1532))))))))))) --> APP(S,S1,S2),
 (exists(S1_1409:exists(v_1407:exists(S1_1564:exists(v_1562:S1_1564= & 
  S1_1564= & S_1453= & v_1407=v_1562 & S1_1409=S1_1414 & S2=S2_1416 & 
  APP(S_1453,S1_1414,S2_1416) & S1=union(S1_1409,{v_1407}) & S=union(S1_1564,
  {v_1562})))))) --> APP(S,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append0$node2~node2 SUCCESS

Checking procedure append1$node2~node2... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  APP1(S,S1,S2)
!!! POST:  S=union(S1,S2)
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [APP1]
              EBase exists (Expl)(Impl)[q; m; S1; p; n; 
                    S2](ex)x::dll<q,m,S1>@M[Orig][LHSCase] * 
                    y::dll<p,n,S2>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 20::
                                EXISTS(Anon_13,t,
                                S: res::dll<Anon_13,t,S>@M[Orig][LHSCase]&
                                t=n+m & APP1(S,S1,S2)&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[q; m; S1; p; n; 
                  S2](ex)x::dll<q,m,S1>@M[Orig][LHSCase] * 
                  y::dll<p,n,S2>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 20::
                              res::dll<Anon_13,t,S>@M[Orig][LHSCase]&t=n+m & 
                              S=union(S1,S2) & 0<=m & 0<=n&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(S1_1713:exists(v_1711:exists(v_2095:exists(S1_2097:S=union(S1_2097,
  {v_2095}) & S1=union(S1_1713,{v_1711}) & APP1(S_1800,S1_1721,S2_1724) & 
  S2=S2_1724 & S1_1713=S1_1721 & v_1711=v_2095 & S1_2097=S_1800 & S_1800= & 
  S1_2097= & S1_2097=))))) --> APP1(S,S1,S2),
 (exists(S1_1932:exists(v_1931:(S2= | S2=union(S1_1932,{v_1931})) & S1= & 
  S2=S))) --> APP1(S,S1,S2),
 (exists(S1_2075:exists(v_2074:exists(S1_1713:exists(v_1711:exists(v_1947:exists(S1_1949:exists(S1_1883:exists(S1_1972:exists(v_1881:exists(v_1970:(S1_1883= | 
  S1_1883=union(S1_2075,{v_2074})) & S=union(S1_1949,{v_1947}) & 
  S1=union(S1_1713,{v_1711}) & APP1(S_1818,S1_1721,S2_1724) & S2=S2_1724 & 
  S1_1713=S1_1721 & v_1711=v_1947 & S_1818=union(S1_1883,{v_1881}) & 
  S1_1949=union(S1_1972,{v_1970}) & S1_1949=union(S1_1972,{v_1970}) & 
  S1_1883=S1_1972 & v_1881=v_1970))))))))))) --> APP1(S,S1,S2),
 (exists(S1_1713:exists(v_1711:exists(S1_2097:exists(v_2095:S1_2097= & 
  S1_2097= & S_1800= & S1_2097=S_1800 & v_1711=v_2095 & S1_1713=S1_1721 & 
  S2=S2_1724 & APP1(S_1800,S1_1721,S2_1724) & S1=union(S1_1713,{v_1711}) & 
  S=union(S1_2097,{v_2095})))))) --> APP1(S,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append1$node2~node2 SUCCESS

Checking procedure append2$node2~node2... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ m!=0, m!=0, m!=0]
!!! REL :  APP2(S,S1,S2)
!!! POST:  S=union(S1,S2)
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [m,APP2]
              EBase exists (Expl)(Impl)[q; m; S1; p; n; 
                    S2](ex)x::dll<q,m,S1>@M[Orig][LHSCase] * 
                    y::dll<p,n,S2>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 25::
                                EXISTS(q_43,t,
                                S: x::dll<q_43,t,S>@M[Orig][LHSCase]&t=n+m & 
                                APP2(S,S1,S2) & q_43=q&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[q; m; S1; p; n; 
                  S2](ex)x::dll<q,m,S1>@M[Orig][LHSCase] * 
                  y::dll<p,n,S2>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                    EBase true&(1<=m | m<=(0-1)) & MayLoop&
                          {FLOW,(1,23)=__flow}
                            EAssume 25::
                              x::dll<q_43,t,S>@M[Orig][LHSCase]&t=n+m & 
                              q_43=q & S=union(S1,S2) & 0<=m & 0<=n&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(v_2350:exists(v_2733:exists(S1_2352:exists(S1_2735:S=union(S1_2735,
  {v_2733}) & S1=union(S1_2352,{v_2350}) & S2= & S1_2735=S2 & 
  v_2350=v_2733 & S1_2352= & S1_2735= & S1_2735=))))) --> APP2(S,S1,S2),
 (exists(S1_2681:exists(v_2680:exists(v_2350:exists(v_2554:exists(v_2476:exists(S1_2478:exists(S1_2352:exists(S1_2556:exists(S1_2584:exists(v_2582:(S1_2478= | 
  S1_2478=union(S1_2681,{v_2680})) & S=union(S1_2556,{v_2554}) & 
  S1=union(S1_2352,{v_2350}) & S2=union(S1_2478,{v_2476}) & v_2350=v_2554 & 
  v_2476=v_2582 & S1_2478=S1_2584 & S1_2352= & S1_2556=union(S1_2584,
  {v_2582}) & S1_2556=union(S1_2584,{v_2582})))))))))))) --> APP2(S,S1,S2),
 (exists(S1_2352:exists(v_2350:exists(S1_2735:exists(v_2733:S1_2735= & 
  S1_2735= & S1_2352= & v_2350=v_2733 & S1_2735=S2 & S2= & S1=union(S1_2352,
  {v_2350}) & S=union(S1_2735,{v_2733})))))) --> APP2(S,S1,S2),
 (exists(S1_2939:exists(v_2938:exists(S1_2352:exists(v_2350:exists(S1_2866:exists(v_2864:S_2863=union(S1_2939,
  {v_2938}) & S_2863=S1_2866 & v_2350=v_2864 & S1_2352=S1_2493 & 
  S2=S2_2496 & APP2(S_2863,S1_2493,S2_2496) & S1=union(S1_2352,{v_2350}) & 
  S=union(S1_2866,{v_2864})))))))) --> APP2(S,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append2$node2~node2 SUCCESS

Checking procedure insert$node2~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  INSERT(S,S1,a)
!!! POST:  S1=union(S,{a})
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [INSERT]
              EBase exists (Expl)(Impl)[p; n; 
                    S](ex)x::dll<p,n,S>@M[Orig][LHSCase]&x!=null&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::
                                EXISTS(p_48,m,
                                S1: x::dll<p_48,m,S1>@M[Orig][LHSCase]&m=1+
                                n & INSERT(S,S1,a) & p_48=p&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p; n; 
                  S](ex)x::dll<p,n,S>@M[Orig][LHSCase]&x!=null&
                  {FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 1::
                              x::dll<p_48,m,S1>@M[Orig][LHSCase]&m=1+n & 
                              p_48=p & S1=union(S,{a}) & 0<=n&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(S1_3241:exists(v_3239:exists(S1_3135:exists(v_3133:exists(S1_3222:exists(v_3220:S1_3241= & 
  S1_3222=union(S1_3241,{v_3239}) & S1_3222=union(S1_3241,{v_3239}) & 
  S1_3135= & v_3133=v_3220 & a=v_3239 & S=union(S1_3135,{v_3133}) & 
  S1=union(S1_3222,{v_3220})))))))) --> INSERT(S,S1,a),
 (exists(S1_3378:exists(v_3377:exists(S1_3135:exists(v_3133:exists(S1_3309:exists(v_3307:S1_3306=union(S1_3378,
  {v_3377}) & S1_3306=S1_3309 & v_3133=v_3307 & S1_3135=S_3187 & 
  INSERT(S_3187,S1_3306,a) & S=union(S1_3135,{v_3133}) & S1=union(S1_3309,
  {v_3307})))))))) --> INSERT(S,S1,a)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert$node2~int SUCCESS

Termination checking result:


0 false contexts at: ()

Total verification time: 31.61 second(s)
	Time spent in main process: 3.76 second(s)
	Time spent in child processes: 27.85 second(s)

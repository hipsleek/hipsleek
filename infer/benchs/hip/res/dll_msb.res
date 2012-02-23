/usr/local/bin/mona

Processing file "dll_msb.ss"
Parsing dll_msb.ss ...
Parsing ../../../prelude.ss ...
Starting Reduce... 
Translating global variables to procedure parameters...

Checking procedure append$node2~node2... Starting Omega...oc

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

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
!!! NEW RELS:[ (exists(S1_1023:exists(v_1022:(S2= | S2=union(S1_1023,{v_1022})) & S1= & 
  S2=S))) --> APP(S,S1,S2),
 (exists(S1_1121:exists(v_1120:exists(S1_833:exists(v_831:exists(v_1039:exists(S1_1041:exists(S1_988:exists(S1_1058:exists(v_986:exists(v_1056:(S1_988= | 
  S1_988=union(S1_1121,{v_1120})) & S=union(S1_1041,{v_1039}) & 
  S1=union(S1_833,{v_831}) & APP(S_926,S1_839,S2_842) & S2=S2_842 & 
  S1_833=S1_839 & v_831=v_1039 & S_926=union(S1_988,{v_986}) & 
  S1_1041=union(S1_1058,{v_1056}) & S1_1041=union(S1_1058,{v_1056}) & 
  S1_988=S1_1058 & v_986=v_1056))))))))))) --> APP(S,S1,S2),
 (exists(S1_833:exists(v_831:exists(S1_1143:exists(v_1141:S1_1143= & 
  S1_1143= & S_914= & v_831=v_1141 & S1_833=S1_839 & S2=S2_842 & 
  APP(S_914,S1_839,S2_842) & S1=union(S1_833,{v_831}) & S=union(S1_1143,
  {v_1141})))))) --> APP(S,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append$node2~node2 SUCCESS

Checking procedure append0$node2~node2... 
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
!!! NEW RELS:[ (exists(S1_1341:exists(v_1340:(S2= | S2=union(S1_1341,{v_1340})) & S1= & 
  S2=S))) --> APP(S,S1,S2),
 (exists(S1_1386:exists(v_1385:exists(S1_1234:exists(v_1232:exists(v_1344:exists(S1_1346:exists(S1_1317:exists(S1_1359:exists(v_1315:exists(v_1357:(S1_1317= | 
  S1_1317=union(S1_1386,{v_1385})) & S=union(S1_1346,{v_1344}) & 
  S1=union(S1_1234,{v_1232}) & APP(S_1282,S1_1239,S2_1241) & S2=S2_1241 & 
  S1_1234=S1_1239 & v_1232=v_1344 & S_1282=union(S1_1317,{v_1315}) & 
  S1_1346=union(S1_1359,{v_1357}) & S1_1346=union(S1_1359,{v_1357}) & 
  S1_1317=S1_1359 & v_1315=v_1357))))))))))) --> APP(S,S1,S2),
 (exists(S1_1234:exists(v_1232:exists(S1_1389:exists(v_1387:S1_1389= & 
  S1_1389= & S_1278= & v_1232=v_1387 & S1_1234=S1_1239 & S2=S2_1241 & 
  APP(S_1278,S1_1239,S2_1241) & S1=union(S1_1234,{v_1232}) & S=union(S1_1389,
  {v_1387})))))) --> APP(S,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append0$node2~node2 SUCCESS

Checking procedure append1$node2~node2... 
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
!!! NEW RELS:[ (exists(S1_1492:exists(v_1490:exists(v_1794:exists(S1_1796:S=union(S1_1796,
  {v_1794}) & S1=union(S1_1492,{v_1490}) & APP1(S_1573,S1_1498,S2_1501) & 
  S2=S2_1501 & S1_1492=S1_1498 & v_1490=v_1794 & S1_1796=S_1573 & S_1573= & 
  S1_1796= & S1_1796=))))) --> APP1(S,S1,S2),
 (exists(S1_1677:exists(v_1676:(S2= | S2=union(S1_1677,{v_1676})) & S1= & 
  S2=S))) --> APP1(S,S1,S2),
 (exists(S1_1774:exists(v_1773:exists(S1_1492:exists(v_1490:exists(v_1692:exists(S1_1694:exists(S1_1644:exists(S1_1711:exists(v_1642:exists(v_1709:(S1_1644= | 
  S1_1644=union(S1_1774,{v_1773})) & S=union(S1_1694,{v_1692}) & 
  S1=union(S1_1492,{v_1490}) & APP1(S_1585,S1_1498,S2_1501) & S2=S2_1501 & 
  S1_1492=S1_1498 & v_1490=v_1692 & S_1585=union(S1_1644,{v_1642}) & 
  S1_1694=union(S1_1711,{v_1709}) & S1_1694=union(S1_1711,{v_1709}) & 
  S1_1644=S1_1711 & v_1642=v_1709))))))))))) --> APP1(S,S1,S2),
 (exists(S1_1492:exists(v_1490:exists(S1_1796:exists(v_1794:S1_1796= & 
  S1_1796= & S_1573= & S1_1796=S_1573 & v_1490=v_1794 & S1_1492=S1_1498 & 
  S2=S2_1501 & APP1(S_1573,S1_1498,S2_1501) & S1=union(S1_1492,{v_1490}) & 
  S=union(S1_1796,{v_1794})))))) --> APP1(S,S1,S2)]
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
!!! NEW RELS:[ (exists(v_1902:exists(v_2221:exists(S1_1904:exists(S1_2223:S=union(S1_2223,
  {v_2221}) & S1=union(S1_1904,{v_1902}) & S2= & S1_2223=S2 & 
  v_1902=v_2221 & S1_1904= & S1_2223= & S1_2223=))))) --> APP2(S,S1,S2),
 (exists(S1_2169:exists(v_2168:exists(v_1902:exists(v_2080:exists(v_2012:exists(S1_2014:exists(S1_1904:exists(S1_2082:exists(S1_2106:exists(v_2104:(S1_2014= | 
  S1_2014=union(S1_2169,{v_2168})) & S=union(S1_2082,{v_2080}) & 
  S1=union(S1_1904,{v_1902}) & S2=union(S1_2014,{v_2012}) & v_1902=v_2080 & 
  v_2012=v_2104 & S1_2014=S1_2106 & S1_1904= & S1_2082=union(S1_2106,
  {v_2104}) & S1_2082=union(S1_2106,{v_2104})))))))))))) --> APP2(S,S1,S2),
 (exists(S1_1904:exists(v_1902:exists(S1_2223:exists(v_2221:S1_2223= & 
  S1_2223= & S1_1904= & v_1902=v_2221 & S1_2223=S2 & S2= & S1=union(S1_1904,
  {v_1902}) & S=union(S1_2223,{v_2221})))))) --> APP2(S,S1,S2),
 (exists(S1_2389:exists(v_2388:exists(S1_1904:exists(v_1902:exists(S1_2336:exists(v_2334:S_2333=union(S1_2389,
  {v_2388}) & S_2333=S1_2336 & v_1902=v_2334 & S1_1904=S1_2023 & 
  S2=S2_2026 & APP2(S_2333,S1_2023,S2_2026) & S1=union(S1_1904,{v_1902}) & 
  S=union(S1_2336,{v_2334})))))))) --> APP2(S,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append2$node2~node2 SUCCESS

Checking procedure insert$node2~int... 
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
!!! NEW RELS:[ (exists(S1_2534:exists(v_2532:exists(S1_2446:exists(v_2444:exists(S1_2517:exists(v_2515:S1_2534= & 
  S1_2517=union(S1_2534,{v_2532}) & S1_2517=union(S1_2534,{v_2532}) & 
  S1_2446= & v_2444=v_2515 & a=v_2532 & S=union(S1_2446,{v_2444}) & 
  S1=union(S1_2517,{v_2515})))))))) --> INSERT(S,S1,a),
 (exists(S1_2635:exists(v_2634:exists(S1_2446:exists(v_2444:exists(S1_2586:exists(v_2584:S1_2583=union(S1_2635,
  {v_2634}) & S1_2583=S1_2586 & v_2444=v_2584 & S1_2446=S_2486 & 
  INSERT(S_2486,S1_2583,a) & S=union(S1_2446,{v_2444}) & S1=union(S1_2586,
  {v_2584})))))))) --> INSERT(S,S1,a)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert$node2~int SUCCESS

Termination checking result:


0 false contexts at: ()

Total verification time: 18.93 second(s)
	Time spent in main process: 2.58 second(s)
	Time spent in child processes: 16.35 second(s)

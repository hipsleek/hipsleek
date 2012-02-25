/usr/local/bin/mona

Processing file "complete_mshb.ss"
Parsing complete_mshb.ss ...
Parsing ../../../prelude.ss ...
Starting Reduce... 
Translating global variables to procedure parameters...
Starting Omega...oc

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Checking procedure count$node2... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]:Timeout exception

[mona.ml]: Mona is preparing to restart because of Timeout when checking #999!
Restarting Mona ...

[mona.ml]:Timeout exception

[mona.ml]: Mona is preparing to restart because of Timeout when checking #999!
Restarting Mona ...

!!! REL :  CNT(S2,S1)
!!! POST:  S1=S2
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [CNT]
              EBase exists (Expl)(Impl)[n; h; nmin; 
                    S1](ex)t::complete1<n,h,nmin,S1>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                    (([true][nmin<=h]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 5::
                                EXISTS(n_73,h_74,nmin_75,
                                S2: t::complete1<n_73,h_74,nmin_75,S2>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                                (
                                ([true][CNT(S2,S1)][n=n_73]
                                 [h_74=h & nmin=nmin_75 & nmin_75<=h_74]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; h; nmin; 
                  S1](ex)t::complete1<n,h,nmin,S1>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                  (([nmin<=h]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 5::
                              t::complete1<n_73,h_74,nmin_75,S2>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                              (
                              ([S2=S1]
                               [h=h_74 & nmin_75=nmin & nmin<=h & 0<=nmin]
                               [n_73=n & 0<=n]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (S2= & S2=S1) --> CNT(S2,S1),
 (S1=S2 & S2=) --> CNT(S2,S1),
 (exists(S2_1682:exists(S1_1678:exists(v_1289:exists(v_1674:exists(S2_1297:exists(S1_1293:S1=union(S1_1293,
  S2_1297,{v_1289}) & S2=union(S1_1678,S2_1682,{v_1674}) & S1!=() & 
  CNT(S2_1445,S1_1327) & CNT(S2_1543,S1_1455) & S2_1543=S2_1682 & 
  S2_1445=S1_1678 & v_1289=v_1674 & S2_1297=S1_1455 & S1_1293=S1_1327 & 
  S1_1293!=() & S2_1445!=()))))))) --> CNT(S2,S1),
 (exists(S2_1856:exists(S1_1852:exists(v_1312:exists(v_1848:exists(S2_1320:exists(S1_1316:S1!=() & 
  S2=union(S1_1852,S2_1856,{v_1848}) & S1=union(S1_1316,S2_1320,{v_1312}) & 
  CNT(S2_1448,S1_1327) & CNT(S2_1562,S1_1455) & S2_1562=S2_1856 & 
  S2_1448=S1_1852 & v_1312=v_1848 & S2_1320=S1_1455 & 
  S1_1316=S1_1327))))))) --> CNT(S2,S1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure count$node2 SUCCESS

Checking procedure maxim$int~int... 
Procedure maxim$int~int SUCCESS

Checking procedure height$node2... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of mona aborted execution
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of mona aborted execution
Restarting Mona ...

!!! REL :  HGT(S1,S2)
!!! POST:  S1=S2
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [HGT]
              EBase exists (Expl)(Impl)[n; h; nmin; 
                    S1](ex)t::complete1<n,h,nmin,S1>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                    (([true][nmin<=h]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 11::
                                EXISTS(n_70,h_71,nmin_72,
                                S2: t::complete1<n_70,h_71,nmin_72,S2>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                                (
                                ([HGT(S1,S2)][n=n_70]
                                 [nmin_72=nmin & h=h_71 & h=res & 
                                   nmin_72<=h_71]
                                 ))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; h; nmin; 
                  S1](ex)t::complete1<n,h,nmin,S1>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                  (([nmin<=h]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 11::
                              t::complete1<n_70,h_71,nmin_72,S2>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                              (
                              ([S2=S1]
                               [nmin=nmin_72 & res=h & res=h_71 & nmin<=h & 
                                 0<=nmin]
                               [n_70=n & 0<=n]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (S2= & S2=S1) --> HGT(S1,S2),
 (exists(S2_2615:exists(S1_2611:exists(v_2219:exists(v_2607:exists(S2_2227:exists(S1_2223:S1=union(S1_2223,
  S2_2227,{v_2219}) & S2=union(S1_2611,S2_2615,{v_2607}) & S1!=() & 
  HGT(S1_2257,S2_2375) & HGT(S1_2385,S2_2469) & S2_2469=S2_2615 & 
  S2_2375=S1_2611 & v_2219=v_2607 & S1_2257=S1_2223 & S1_2385=S2_2227 & 
  S1_2223!=() & S2_2375!=()))))))) --> HGT(S1,S2),
 (exists(S2_2820:exists(S1_2816:exists(v_2242:exists(v_2812:exists(S1_2246:exists(S2_2250:S1!=() & 
  S2=union(S1_2816,S2_2820,{v_2812}) & S1=union(S1_2246,S2_2250,{v_2242}) & 
  HGT(S1_2257,S2_2378) & HGT(S1_2385,S2_2487) & S2_2487=S2_2820 & 
  S2_2378=S1_2816 & v_2242=v_2812 & S1_2257=S1_2246 & 
  S1_2385=S2_2250))))))) --> HGT(S1,S2),
 (S1=S2 & S2=) --> HGT(S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure height$node2 SUCCESS

Checking procedure insert$node2~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure insert$node2~int SUCCESS

Checking procedure is_perfect$node2... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure is_perfect$node2 SUCCESS

Checking procedure minim$int~int... 
Procedure minim$int~int SUCCESS

Checking procedure min_height$node2... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of mona aborted execution
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of mona aborted execution
Restarting Mona ...

!!! REL :  MHGT(S1,S2)
!!! POST:  S1=S2
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [MHGT]
              EBase exists (Expl)(Impl)[n; h; nmin; 
                    S1](ex)t::complete1<n,h,nmin,S1>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                    (([true][nmin<=h]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 15::
                                EXISTS(n_63,h_64,nmin_65,
                                S2: t::complete1<n_63,h_64,nmin_65,S2>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                                (
                                ([MHGT(S1,S2)][n=n_63]
                                 [h_64=h & nmin=nmin_65 & nmin=res & 
                                   nmin_65<=h_64]
                                 ))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; h; nmin; 
                  S1](ex)t::complete1<n,h,nmin,S1>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                  (([nmin<=h]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 15::
                              t::complete1<n_63,h_64,nmin_65,S2>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                              (
                              ([S2=S1]
                               [h=h_64 & res=nmin & res=nmin_65 & nmin<=h & 
                                 0<=nmin]
                               [n_63=n & 0<=n]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (S2= & S2=S1) --> MHGT(S1,S2),
 (exists(S2_8235:exists(S1_8231:exists(v_7839:exists(v_8227:exists(S2_7847:exists(S1_7843:S1=union(S1_7843,
  S2_7847,{v_7839}) & S2=union(S1_8231,S2_8235,{v_8227}) & S1!=() & 
  MHGT(S1_7877,S2_7995) & MHGT(S1_8005,S2_8089) & S2_8089=S2_8235 & 
  S2_7995=S1_8231 & v_7839=v_8227 & S1_7877=S1_7843 & S1_8005=S2_7847 & 
  S1_7843!=() & S2_7995!=()))))))) --> MHGT(S1,S2),
 (exists(S2_8458:exists(S1_8454:exists(v_7862:exists(v_8450:exists(S1_7866:exists(S2_7870:S1!=() & 
  S2=union(S1_8454,S2_8458,{v_8450}) & S1=union(S1_7866,S2_7870,{v_7862}) & 
  MHGT(S1_7877,S2_7998) & MHGT(S1_8005,S2_8107) & S2_8107=S2_8458 & 
  S2_7998=S1_8454 & v_7862=v_8450 & S1_7877=S1_7866 & 
  S1_8005=S2_7870))))))) --> MHGT(S1,S2),
 (S1=S2 & S2=) --> MHGT(S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure min_height$node2 SUCCESS

Termination checking result:


30 false contexts at: ( (144,12)  (143,12)  (142,12)  (141,18)  (141,12)  (141,12)  (130,10)  (129,10)  (128,10)  (127,16)  (127,10)  (127,10)  (123,8)  (122,8)  (121,8)  (120,14)  (120,8)  (120,8)  (138,12)  (137,12)  (136,12)  (135,18)  (135,12)  (135,12)  (116,2)  (115,25)  (115,19)  (115,6)  (115,2)  (115,2) )

Total verification time: 190.87 second(s)
	Time spent in main process: 7.35 second(s)
	Time spent in child processes: 183.52 second(s)

/usr/local/bin/mona

Processing file "complete_mshb.ss"
Parsing complete_mshb.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
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

[mona.ml]: Mona is preparing to restart because of upper limit reached
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
                                EXISTS(n_72,h_73,nmin_74,
                                S2: t::complete1<n_72,h_73,nmin_74,S2>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                                (
                                ([true][CNT(S2,S1)][n=n_72]
                                 [h_73=h & nmin=nmin_74 & nmin_74<=h_73]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; h; nmin; 
                  S1](ex)t::complete1<n,h,nmin,S1>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                  (([nmin<=h]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 5::
                              EXISTS(n_2062,h_2063,nmin_2064,
                              S2_2065: t::complete1<n_2062,h_2063,nmin_2064,S2_2065>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                              (
                              ([S1=S2_2065]
                               [nmin=nmin_2064 & h=h_2063 & nmin<=h & 0<=nmin]
                               [n=n_2062 & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
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

[mona.ml]: Mona is preparing to restart because of upper limit reached
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
                                EXISTS(n_69,h_70,nmin_71,
                                S2: t::complete1<n_69,h_70,nmin_71,S2>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                                (
                                ([HGT(S1,S2)][n=n_69]
                                 [nmin_71=nmin & h=h_70 & h=res & 
                                   nmin_71<=h_70]
                                 ))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; h; nmin; 
                  S1](ex)t::complete1<n,h,nmin,S1>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                  (([nmin<=h]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 11::
                              EXISTS(n_3063,h_3064,nmin_3065,
                              S2_3066: t::complete1<n_3063,h_3064,nmin_3065,S2_3066>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                              (
                              ([S1=S2_3066]
                               [nmin=nmin_3065 & res=h & res=h_3064 & 
                                 nmin<=h & 0<=nmin]
                               [n=n_3063 & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S2= & S2=S1) --> HGT(S1,S2),
 (exists(S2_2584:exists(S1_2580:exists(v_2188:exists(v_2576:exists(S2_2196:exists(S1_2192:S1=union(S1_2192,
  S2_2196,{v_2188}) & S2=union(S1_2580,S2_2584,{v_2576}) & S1!=() & 
  HGT(S1_2226,S2_2344) & HGT(S1_2354,S2_2438) & S2_2438=S2_2584 & 
  S2_2344=S1_2580 & v_2188=v_2576 & S1_2226=S1_2192 & S1_2354=S2_2196 & 
  S1_2192!=() & S2_2344!=()))))))) --> HGT(S1,S2),
 (exists(S2_2789:exists(S1_2785:exists(v_2211:exists(v_2781:exists(S1_2215:exists(S2_2219:S1!=() & 
  S2=union(S1_2785,S2_2789,{v_2781}) & S1=union(S1_2215,S2_2219,{v_2211}) & 
  HGT(S1_2226,S2_2347) & HGT(S1_2354,S2_2456) & S2_2456=S2_2789 & 
  S2_2347=S1_2785 & v_2211=v_2781 & S1_2226=S1_2215 & 
  S1_2354=S2_2219))))))) --> HGT(S1,S2),
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

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  PEF(S1,S2)
!!! POST:  S1=S2
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [PEF]
              EBase exists (Expl)(Impl)[k; n; nmin; 
                    S1](ex)t::complete1<k,n,nmin,S1>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                    (([true][nmin<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 34::
                                EXISTS(k_49,n_50,nmin_51,
                                S2: t::complete1<k_49,n_50,nmin_51,S2>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                                (
                                ([PEF(S1,S2)][k=k_49]
                                 [n=n_50 & nmin=nmin_51 & (nmin!=n | 
                                   res=1) & (nmin=n | res=0) & nmin_51<=n_50]
                                 ))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[k; n; nmin; 
                  S1](ex)t::complete1<k,n,nmin,S1>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                  (([nmin<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 34::
                              EXISTS(k_7716,n_7717,nmin_7718,
                              S2_7719: t::complete1<k_7716,n_7717,nmin_7718,S2_7719>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                              (
                              ([S1=S2_7719]
                               [nmin=nmin_7718 & n=n_7717 & (nmin!=n | 
                                 res=1) & (nmin=n | res=0) & nmin<=n & 
                                 0<=nmin]
                               [k=k_7716 & 0<=k]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S2= & S2=S1) --> PEF(S1,S2),
 (S1=S2 & S2=) --> PEF(S1,S2),
 (exists(S_6765:exists(S2_7143:exists(S2_6617:exists(S1_7139:exists(S:exists(v_6609:exists(v_7135:exists(S1_6613:S1!=() & 
  S2=union(S1_7139,S2_7143,{v_7135}) & S1=union(S1_6613,S2_6617,{v_6609}) & 
  S_6765=S2_6617 & S2_7143=S2_6617 & S1_6613=S & S1_7139=S & v_6609=v_7135 & 
  S1_6613!=()))))))))) --> PEF(S1,S2),
 (exists(S2_7336:exists(S1_7332:exists(v_6632:exists(v_7328:exists(S2_6640:exists(S_6765:exists(S:exists(S1_6636:S1!=() & 
  S2=union(S1_7332,S2_7336,{v_7328}) & S1=union(S1_6636,S2_6640,{v_6632}) & 
  PEF(S1_7052,S2_7327) & PEF(S1_6941,S2_6997) & S2_7327=S2_7336 & 
  S2_6997=S1_7332 & v_6632=v_7328 & S2_6640=S_6765 & S1_7052=S_6765 & 
  S=S1_6636 & S1_6941=S1_6636))))))))) --> PEF(S1,S2),
 (exists(S_6765:exists(S2_7549:exists(S2_6640:exists(S1_7545:exists(v_6632:exists(v_7541:exists(S1_6636:exists(S:S2=union(S1_7545,
  S2_7549,{v_7541}) & S1=union(S1_6636,S2_6640,{v_6632}) & S1!=() & 
  PEF(S1_6941,S2_7018) & S_6765=S2_6640 & S2_7549=S2_6640 & 
  S2_7018=S1_7545 & v_6632=v_7541 & S1_6636=S & 
  S1_6941=S))))))))) --> PEF(S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
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

[mona.ml]: Mona is preparing to restart because of upper limit reached
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
                                EXISTS(n_62,h_63,nmin_64,
                                S2: t::complete1<n_62,h_63,nmin_64,S2>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                                (
                                ([MHGT(S1,S2)][n=n_62]
                                 [h_63=h & nmin=nmin_64 & nmin=res & 
                                   nmin_64<=h_63]
                                 ))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; h; nmin; 
                  S1](ex)t::complete1<n,h,nmin,S1>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                  (([nmin<=h]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 15::
                              EXISTS(n_8727,h_8728,nmin_8729,
                              S2_8730: t::complete1<n_8727,h_8728,nmin_8729,S2_8730>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                              (
                              ([S1=S2_8730]
                               [res=nmin & res=nmin_8729 & h=h_8728 & 
                                 nmin<=h & 0<=nmin]
                               [n=n_8727 & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S2= & S2=S1) --> MHGT(S1,S2),
 (exists(S2_8236:exists(S1_8232:exists(v_7840:exists(v_8228:exists(S2_7848:exists(S1_7844:S1=union(S1_7844,
  S2_7848,{v_7840}) & S2=union(S1_8232,S2_8236,{v_8228}) & S1!=() & 
  MHGT(S1_7878,S2_7996) & MHGT(S1_8006,S2_8090) & S2_8090=S2_8236 & 
  S2_7996=S1_8232 & v_7840=v_8228 & S1_7878=S1_7844 & S1_8006=S2_7848 & 
  S1_7844!=() & S2_7996!=()))))))) --> MHGT(S1,S2),
 (exists(S2_8454:exists(S1_8450:exists(v_7863:exists(v_8446:exists(S1_7867:exists(S2_7871:S1!=() & 
  S2=union(S1_8450,S2_8454,{v_8446}) & S1=union(S1_7867,S2_7871,{v_7863}) & 
  MHGT(S1_7878,S2_7999) & MHGT(S1_8006,S2_8108) & S2_8108=S2_8454 & 
  S2_7999=S1_8450 & v_7863=v_8446 & S1_7878=S1_7867 & 
  S1_8006=S2_7871))))))) --> MHGT(S1,S2),
 (S1=S2 & S2=) --> MHGT(S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure min_height$node2 SUCCESS

Termination checking result:


30 false contexts at: ( (145,12)  (144,12)  (143,12)  (142,18)  (142,12)  (142,12)  (131,10)  (130,10)  (129,10)  (128,16)  (128,10)  (128,10)  (124,8)  (123,8)  (122,8)  (121,14)  (121,8)  (121,8)  (139,12)  (138,12)  (137,12)  (136,18)  (136,12)  (136,12)  (117,2)  (116,25)  (116,19)  (116,6)  (116,2)  (116,2) )

Total verification time: 102.88 second(s)
	Time spent in main process: 3.24 second(s)
	Time spent in child processes: 99.64 second(s)

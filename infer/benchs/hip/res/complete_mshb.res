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
                              EXISTS(n_8565,h_8566,nmin_8567,
                              S2_8568: t::complete1<n_8565,h_8566,nmin_8567,S2_8568>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                              (
                              ([S1=S2_8568]
                               [res=nmin & res=nmin_8567 & h=h_8566 & 
                                 nmin<=h & 0<=nmin]
                               [n=n_8565 & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S2= & S2=S1) --> MHGT(S1,S2),
 (exists(S2_8074:exists(S1_8070:exists(v_7678:exists(v_8066:exists(S2_7686:exists(S1_7682:S1=union(S1_7682,
  S2_7686,{v_7678}) & S2=union(S1_8070,S2_8074,{v_8066}) & S1!=() & 
  MHGT(S1_7716,S2_7834) & MHGT(S1_7844,S2_7928) & S2_7928=S2_8074 & 
  S2_7834=S1_8070 & v_7678=v_8066 & S1_7716=S1_7682 & S1_7844=S2_7686 & 
  S1_7682!=() & S2_7834!=()))))))) --> MHGT(S1,S2),
 (exists(S2_8292:exists(S1_8288:exists(v_7701:exists(v_8284:exists(S1_7705:exists(S2_7709:S1!=() & 
  S2=union(S1_8288,S2_8292,{v_8284}) & S1=union(S1_7705,S2_7709,{v_7701}) & 
  MHGT(S1_7716,S2_7837) & MHGT(S1_7844,S2_7946) & S2_7946=S2_8292 & 
  S2_7837=S1_8288 & v_7701=v_8284 & S1_7716=S1_7705 & 
  S1_7844=S2_7709))))))) --> MHGT(S1,S2),
 (S1=S2 & S2=) --> MHGT(S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure min_height$node2 SUCCESS

Termination checking result:


30 false contexts at: ( (150,12)  (149,12)  (148,12)  (147,18)  (147,12)  (147,12)  (136,10)  (135,10)  (134,10)  (133,16)  (133,10)  (133,10)  (129,8)  (128,8)  (127,8)  (126,14)  (126,8)  (126,8)  (144,12)  (143,12)  (142,12)  (141,18)  (141,12)  (141,12)  (122,2)  (121,25)  (121,19)  (121,6)  (121,2)  (121,2) )

Total verification time: 95.78 second(s)
	Time spent in main process: 1.46 second(s)
	Time spent in child processes: 94.32 second(s)

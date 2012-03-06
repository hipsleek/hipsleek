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
                              EXISTS(n_2031,h_2032,nmin_2033,
                              S2_2034: t::complete1<n_2031,h_2032,nmin_2033,S2_2034>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                              (
                              ([S1=S2_2034]
                               [nmin=nmin_2033 & h=h_2032 & nmin<=h & 0<=nmin]
                               [n=n_2031 & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S2= & S2=S1) --> CNT(S2,S1),
 (S1=S2 & S2=) --> CNT(S2,S1),
 (exists(S2_1682:exists(S1_1678:exists(v_1289:exists(v_1674:exists(S2_1297:exists(S1_1293:S1=union(S1_1293,
  S2_1297,{v_1289}) & S2=union(S1_1678,S2_1682,{v_1674}) & S1!=() & 
  CNT(S2_1445,S1_1327) & CNT(S2_1543,S1_1455) & S2_1543=S2_1682 & 
  S2_1445=S1_1678 & v_1289=v_1674 & S2_1297=S1_1455 & S1_1293=S1_1327 & 
  S1_1293!=() & S2_1445!=()))))))) --> CNT(S2,S1),
 (exists(S2_1836:exists(S1_1832:exists(v_1312:exists(v_1828:exists(S2_1320:exists(S1_1316:S1!=() & 
  S2=union(S1_1832,S2_1836,{v_1828}) & S1=union(S1_1316,S2_1320,{v_1312}) & 
  CNT(S2_1448,S1_1327) & CNT(S2_1562,S1_1455) & S2_1562=S2_1836 & 
  S2_1448=S1_1832 & v_1312=v_1828 & S2_1320=S1_1455 & 
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
                              EXISTS(n_2989,h_2990,nmin_2991,
                              S2_2992: t::complete1<n_2989,h_2990,nmin_2991,S2_2992>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                              (
                              ([S1=S2_2992]
                               [nmin=nmin_2991 & res=h & res=h_2990 & 
                                 nmin<=h & 0<=nmin]
                               [n=n_2989 & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S2= & S2=S1) --> HGT(S1,S2),
 (exists(S2_2553:exists(S1_2549:exists(v_2157:exists(v_2545:exists(S2_2165:exists(S1_2161:S1=union(S1_2161,
  S2_2165,{v_2157}) & S2=union(S1_2549,S2_2553,{v_2545}) & S1!=() & 
  HGT(S1_2195,S2_2313) & HGT(S1_2323,S2_2407) & S2_2407=S2_2553 & 
  S2_2313=S1_2549 & v_2157=v_2545 & S1_2195=S1_2161 & S1_2323=S2_2165 & 
  S1_2161!=() & S2_2313!=()))))))) --> HGT(S1,S2),
 (exists(S2_2736:exists(S1_2732:exists(v_2180:exists(v_2728:exists(S1_2184:exists(S2_2188:S1!=() & 
  S2=union(S1_2732,S2_2736,{v_2728}) & S1=union(S1_2184,S2_2188,{v_2180}) & 
  HGT(S1_2195,S2_2316) & HGT(S1_2323,S2_2425) & S2_2425=S2_2736 & 
  S2_2316=S1_2732 & v_2180=v_2728 & S1_2195=S1_2184 & 
  S1_2323=S2_2188))))))) --> HGT(S1,S2),
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
                              EXISTS(k_7600,n_7601,nmin_7602,
                              S2_7603: t::complete1<k_7600,n_7601,nmin_7602,S2_7603>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                              (
                              ([S1=S2_7603]
                               [nmin=nmin_7602 & n=n_7601 & (nmin!=n | 
                                 res=1) & (nmin=n | res=0) & nmin<=n & 
                                 0<=nmin]
                               [k=k_7600 & 0<=k]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S2= & S2=S1) --> PEF(S1,S2),
 (S1=S2 & S2=) --> PEF(S1,S2),
 (exists(S_6691:exists(S2_7069:exists(S2_6543:exists(S1_7065:exists(S:exists(v_6535:exists(v_7061:exists(S1_6539:S1!=() & 
  S2=union(S1_7065,S2_7069,{v_7061}) & S1=union(S1_6539,S2_6543,{v_6535}) & 
  S_6691=S2_6543 & S2_7069=S2_6543 & S1_6539=S & S1_7065=S & v_6535=v_7061 & 
  S1_6539!=()))))))))) --> PEF(S1,S2),
 (exists(S2_7243:exists(S1_7239:exists(v_6558:exists(v_7235:exists(S2_6566:exists(S_6691:exists(S:exists(S1_6562:S1!=() & 
  S2=union(S1_7239,S2_7243,{v_7235}) & S1=union(S1_6562,S2_6566,{v_6558}) & 
  PEF(S1_6978,S2_7234) & PEF(S1_6867,S2_6923) & S2_7234=S2_7243 & 
  S2_6923=S1_7239 & v_6558=v_7235 & S2_6566=S_6691 & S1_6978=S_6691 & 
  S=S1_6562 & S1_6867=S1_6562))))))))) --> PEF(S1,S2),
 (exists(S_6691:exists(S2_7445:exists(S2_6566:exists(S1_7441:exists(v_6558:exists(v_7437:exists(S1_6562:exists(S:S2=union(S1_7441,
  S2_7445,{v_7437}) & S1=union(S1_6562,S2_6566,{v_6558}) & S1!=() & 
  PEF(S1_6867,S2_6944) & S_6691=S2_6566 & S2_7445=S2_6566 & 
  S2_6944=S1_7441 & v_6558=v_7437 & S1_6562=S & 
  S1_6867=S))))))))) --> PEF(S1,S2)]
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
                              EXISTS(n_8551,h_8552,nmin_8553,
                              S2_8554: t::complete1<n_8551,h_8552,nmin_8553,S2_8554>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                              (
                              ([S1=S2_8554]
                               [res=nmin & res=nmin_8553 & h=h_8552 & 
                                 nmin<=h & 0<=nmin]
                               [n=n_8551 & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S2= & S2=S1) --> MHGT(S1,S2),
 (exists(S2_8120:exists(S1_8116:exists(v_7724:exists(v_8112:exists(S2_7732:exists(S1_7728:S1=union(S1_7728,
  S2_7732,{v_7724}) & S2=union(S1_8116,S2_8120,{v_8112}) & S1!=() & 
  MHGT(S1_7762,S2_7880) & MHGT(S1_7890,S2_7974) & S2_7974=S2_8120 & 
  S2_7880=S1_8116 & v_7724=v_8112 & S1_7762=S1_7728 & S1_7890=S2_7732 & 
  S1_7728!=() & S2_7880!=()))))))) --> MHGT(S1,S2),
 (exists(S2_8303:exists(S1_8299:exists(v_7747:exists(v_8295:exists(S1_7751:exists(S2_7755:S1!=() & 
  S2=union(S1_8299,S2_8303,{v_8295}) & S1=union(S1_7751,S2_7755,{v_7747}) & 
  MHGT(S1_7762,S2_7883) & MHGT(S1_7890,S2_7992) & S2_7992=S2_8303 & 
  S2_7883=S1_8299 & v_7747=v_8295 & S1_7762=S1_7751 & 
  S1_7890=S2_7755))))))) --> MHGT(S1,S2),
 (S1=S2 & S2=) --> MHGT(S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure min_height$node2 SUCCESS

Termination checking result:


30 false contexts at: ( (145,12)  (144,12)  (143,12)  (142,18)  (142,12)  (142,12)  (131,10)  (130,10)  (129,10)  (128,16)  (128,10)  (128,10)  (124,8)  (123,8)  (122,8)  (121,14)  (121,8)  (121,8)  (139,12)  (138,12)  (137,12)  (136,18)  (136,12)  (136,12)  (117,2)  (116,25)  (116,19)  (116,6)  (116,2)  (116,2) )

Total verification time: 101.44 second(s)
	Time spent in main process: 3. second(s)
	Time spent in child processes: 98.44 second(s)

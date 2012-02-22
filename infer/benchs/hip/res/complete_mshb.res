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

[mona.ml]: Mona is preparing to restart because of mona aborted execution
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of mona aborted execution
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of mona aborted execution
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of mona aborted execution
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of mona aborted execution
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of mona aborted execution
Restarting Mona ...

[mona.ml]:Timeout exception

[mona.ml]: Mona is preparing to restart because of Timeout when checking #999!
Restarting Mona ...

[mona.ml]:Timeout exception

[mona.ml]: Mona is preparing to restart because of Timeout when checking #999!
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of mona aborted execution
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of mona aborted execution
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of mona aborted execution
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
 (exists(S2_1904:exists(S1_1900:exists(v_1289:exists(v_1896:exists(S2_1297:exists(S1_1293:S1=union(S1_1293,
  S2_1297,{v_1289}) & S2=union(S1_1900,S2_1904,{v_1896}) & S1!=() & 
  CNT(S2_1517,S1_1351) & CNT(S2_1687,S1_1551) & S2_1687=S2_1904 & 
  S2_1517=S1_1900 & v_1289=v_1896 & S2_1297=S1_1551 & S1_1293=S1_1351 & 
  S1_1293!=() & S2_1517!=()))))))) --> CNT(S2,S1),
 (exists(S2_2188:exists(S1_2184:exists(v_1324:exists(v_2180:exists(S2_1332:exists(S1_1328:S1!=() & 
  S2=union(S1_2184,S2_2188,{v_2180}) & S1=union(S1_1328,S2_1332,{v_1324}) & 
  CNT(S2_1532,S1_1351) & CNT(S2_1724,S1_1551) & S2_1724=S2_2188 & 
  S2_1532=S1_2184 & v_1324=v_2180 & S2_1332=S1_1551 & 
  S1_1328=S1_1351))))))) --> CNT(S2,S1)]
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

[mona.ml]: Mona is preparing to restart because of mona aborted execution
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of mona aborted execution
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of mona aborted execution
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of mona aborted execution
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of mona aborted execution
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of mona aborted execution
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of mona aborted execution
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
 (exists(S2_3624:exists(S1_3620:exists(v_3012:exists(v_3616:exists(S2_3020:exists(S1_3016:S1=union(S1_3016,
  S2_3020,{v_3012}) & S2=union(S1_3620,S2_3624,{v_3616}) & S1!=() & 
  HGT(S1_3074,S2_3240) & HGT(S1_3274,S2_3406) & S2_3406=S2_3624 & 
  S2_3240=S1_3620 & v_3012=v_3616 & S1_3074=S1_3016 & S1_3274=S2_3020 & 
  S1_3016!=() & S2_3240!=()))))))) --> HGT(S1,S2),
 (exists(S2_3939:exists(S1_3935:exists(v_3047:exists(v_3931:exists(S1_3051:exists(S2_3055:S1!=() & 
  S2=union(S1_3935,S2_3939,{v_3931}) & S1=union(S1_3051,S2_3055,{v_3047}) & 
  HGT(S1_3074,S2_3255) & HGT(S1_3274,S2_3442) & S2_3442=S2_3939 & 
  S2_3255=S1_3935 & v_3047=v_3931 & S1_3074=S1_3051 & 
  S1_3274=S2_3055))))))) --> HGT(S1,S2),
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

[mona.ml]: Mona is preparing to restart because of mona aborted execution
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of mona aborted execution
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of mona aborted execution
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of mona aborted execution
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of mona aborted execution
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of mona aborted execution
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of mona aborted execution
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of mona aborted execution
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...
Timeout when checking #simplify  Restarting Omega after ... 529 invocations Stop Omega... 529 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 530 invocations Stop Omega... 530 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 531 invocations Stop Omega... 531 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 532 invocations Stop Omega... 532 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 533 invocations Stop Omega... 533 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 534 invocations Stop Omega... 534 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 535 invocations Stop Omega... 535 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 536 invocations Stop Omega... 536 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 537 invocations Stop Omega... 537 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 538 invocations Stop Omega... 538 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 539 invocations Stop Omega... 539 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 540 invocations Stop Omega... 540 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 541 invocations Stop Omega... 541 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 542 invocations Stop Omega... 542 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 543 invocations Stop Omega... 543 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 544 invocations Stop Omega... 544 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 545 invocations Stop Omega... 545 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 546 invocations Stop Omega... 546 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 547 invocations Stop Omega... 547 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 548 invocations Stop Omega... 548 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 549 invocations Stop Omega... 549 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 550 invocations Stop Omega... 550 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 551 invocations Stop Omega... 551 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 552 invocations Stop Omega... 552 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 553 invocations Stop Omega... 553 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 554 invocations Stop Omega... 554 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 555 invocations Stop Omega... 555 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 556 invocations Stop Omega... 556 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 557 invocations Stop Omega... 557 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 558 invocations Stop Omega... 558 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 559 invocations Stop Omega... 559 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 560 invocations Stop Omega... 560 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 561 invocations Stop Omega... 561 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 562 invocations Stop Omega... 562 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 563 invocations Stop Omega... 563 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 564 invocations Stop Omega... 564 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 565 invocations Stop Omega... 565 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 566 invocations Stop Omega... 566 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 567 invocations Stop Omega... 567 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 568 invocations Stop Omega... 568 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 569 invocations Stop Omega... 569 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 570 invocations Stop Omega... 570 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 571 invocations Stop Omega... 571 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 572 invocations Stop Omega... 572 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 573 invocations Stop Omega... 573 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 574 invocations Stop Omega... 574 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 575 invocations Stop Omega... 575 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 576 invocations Stop Omega... 576 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 577 invocations Stop Omega... 577 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 578 invocations Stop Omega... 578 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 579 invocations Stop Omega... 579 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 580 invocations Stop Omega... 580 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 581 invocations Stop Omega... 581 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 582 invocations Stop Omega... 582 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 583 invocations Stop Omega... 583 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 584 invocations Stop Omega... 584 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 585 invocations Stop Omega... 585 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 586 invocations Stop Omega... 586 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 587 invocations Stop Omega... 587 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 588 invocations Stop Omega... 588 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 589 invocations Stop Omega... 589 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 590 invocations Stop Omega... 590 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 591 invocations Stop Omega... 591 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 592 invocations Stop Omega... 592 invocations Starting Omega...oc

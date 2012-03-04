/usr/local/bin/mona

Processing file "bst_mshob.ss"
Parsing bst_mshob.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Translating global variables to procedure parameters...
Starting Omega...oc

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Checking procedure append$node2~node2... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  APP(S,S1,S2)
!!! POST:  S=union(S1,S2)
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [APP]
              EBase exists (Expl)(Impl)[Anon_11; m; S1; Anon_12; n; 
                    S2](ex)x::dll<Anon_11,m,S1>@M[Orig][LHSCase]@ rem br[{286,285}] * 
                    y::dll<Anon_12,n,S2>@M[Orig][LHSCase]@ rem br[{286,285}]&
                    (([true][true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::
                                EXISTS(flted_29_111,r,
                                S: res::dll<r,flted_29_111,S>@M[Orig][LHSCase]@ rem br[{286,285}]&
                                (([flted_29_111=m+n][APP(S,S1,S2)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_11; m; S1; Anon_12; n; 
                  S2](ex)x::dll<Anon_11,m,S1>@M[Orig][LHSCase]@ rem br[{286,285}] * 
                  y::dll<Anon_12,n,S2>@M[Orig][LHSCase]@ rem br[{286,285}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 1::
                              EXISTS(flted_29_1386,r_1387,
                              S_1388: res::dll<r_1387,flted_29_1386,S_1388>@M[Orig][LHSCase]@ rem br[{286,285}]&
                              (
                              ([S_1388=union(S1,S2)]
                               [flted_29_1386=m+n & 0<=m & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_1349:exists(v_1141:exists(v_1346:exists(S1_1144:S1!=() & 
  S1=union(S1_1144,{v_1141}) & S=union(S1_1349,{v_1346}) & 
  APP(S_1194,S1_1150,S2_1153) & S2_1153=S2 & S1_1349=S_1194 & 
  v_1141=v_1346 & S1_1144=S1_1150 & S_1194=))))) --> APP(S,S1,S2),
 (S=S2 & S1=) --> APP(S,S1,S2),
 (exists(S1_1255:exists(v_1252:exists(S1_1285:exists(v_1282:exists(S1_1272:exists(v_1269:exists(S1_1144:exists(v_1141:S1_1255=S1_1285 & 
  v_1252=v_1282 & S_1194=union(S1_1255,{v_1252}) & S_1194!=() & 
  S1_1272=union(S1_1285,{v_1282}) & S1_1144=S1_1150 & v_1141=v_1269 & 
  S2_1153=S2 & APP(S_1194,S1_1150,S2_1153) & S=union(S1_1272,{v_1269}) & 
  S1=union(S1_1144,{v_1141}) & S1!=()))))))))) --> APP(S,S1,S2),
 (exists(S1_1349:exists(v_1346:exists(S1_1144:exists(v_1141:S_1194= & 
  S1_1144=S1_1150 & v_1141=v_1346 & S1_1349=S_1194 & S2_1153=S2 & 
  APP(S_1194,S1_1150,S2_1153) & S=union(S1_1349,{v_1346}) & S1=union(S1_1144,
  {v_1141}) & S1!=()))))) --> APP(S,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append$node2~node2 SUCCESS

Checking procedure appendC$node2~node2... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  C(S,S1,S2)
!!! POST:  S=union(S1,S2)
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [C]
              EBase exists (Expl)(Impl)[q; m; S1; p; n; 
                    S2](ex)x::dll<q,m,S1>@M[Orig][LHSCase]@ rem br[{286,285}] * 
                    y::dll<p,n,S2>@M[Orig][LHSCase]@ rem br[{286,285}]&(
                    ([true][true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 8::
                                EXISTS(flted_54_106,Anon_15,
                                S: res::dll<Anon_15,flted_54_106,S>@M[Orig][LHSCase]@ rem br[{286,285}]&
                                (([flted_54_106=m+n][C(S,S1,S2)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[q; m; S1; p; n; 
                  S2](ex)x::dll<q,m,S1>@M[Orig][LHSCase]@ rem br[{286,285}] * 
                  y::dll<p,n,S2>@M[Orig][LHSCase]@ rem br[{286,285}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 8::
                              EXISTS(flted_54_1663,Anon_1664,
                              S_1665: res::dll<Anon_1664,flted_54_1663,S_1665>@M[Orig][LHSCase]@ rem br[{286,285}]&
                              (
                              ([S_1665=union(S1,S2)]
                               [flted_54_1663=m+n & 0<=m & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S=S2 & S1=) --> C(S,S1,S2),
 (exists(S1_1541:exists(v_1538:exists(S1_1575:exists(v_1572:exists(S1_1562:exists(v_1559:exists(S1_1431:exists(v_1428:S1_1541=S1_1575 & 
  v_1538=v_1572 & S_1488=union(S1_1541,{v_1538}) & S_1488!=() & 
  S1_1562=union(S1_1575,{v_1572}) & S1_1431=S1_1437 & v_1428=v_1559 & 
  S2_1440=S2 & C(S_1488,S1_1437,S2_1440) & S=union(S1_1562,{v_1559}) & 
  S1!=() & S1=union(S1_1431,{v_1428})))))))))) --> C(S,S1,S2),
 (exists(S1_1639:exists(v_1636:exists(S1_1431:exists(v_1428:S_1480= & 
  S1_1639= & S1_1437=S1_1431 & v_1428=v_1636 & S2=S2_1440 & 
  C(S_1480,S1_1437,S2_1440) & S=union(S1_1639,{v_1636}) & S1!=() & 
  S1=union(S1_1431,{v_1428})))))) --> C(S,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure appendC$node2~node2 SUCCESS

Checking procedure count$node2... 
Procedure count$node2 SUCCESS

Checking procedure remove_min$node2... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure remove_min$node2 SUCCESS

Checking procedure delete$node2~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

assert:bst_mshob.ss:186: 16:  : ok


[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure delete$node2~int SUCCESS

Checking procedure flatten$node2... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure flatten$node2 SUCCESS

Checking procedure insert$node2~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...
MONA translation failure!
Context of Verification Failure: File "bst_mshob.ss",Line:119,Col:10
Last Proving Location: File "bst_mshob.ss",Line:132,Col:19

ERROR: at _0_0 
Message: Mona translation failure!!
Error in file monatemp near line  syntax error
 
[mona.ml]:Unexpected exception

Procedure insert$node2~int FAIL-2

Exception Failure("Mona translation failure!!\nError in file monatemp near line  syntax error") Occurred!

Error(s) detected when checking procedure insert$node2~int

Checking procedure search$node2~int... 
Procedure search$node2~int SUCCESS

Checking procedure traverse$node2... 
Procedure traverse$node2 SUCCESS

Termination checking result:


0 false contexts at: ()

Total verification time: 15.1 second(s)
	Time spent in main process: 1.45 second(s)
	Time spent in child processes: 13.65 second(s)

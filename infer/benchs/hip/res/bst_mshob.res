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
                              EXISTS(flted_29_1383,r_1384,
                              S_1385: res::dll<r_1384,flted_29_1383,S_1385>@M[Orig][LHSCase]@ rem br[{286,285}]&
                              (
                              ([S_1385=union(S1,S2)]
                               [flted_29_1383=m+n & 0<=m & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_1346:exists(v_1138:exists(v_1343:exists(S1_1141:S1!=() & 
  S1=union(S1_1141,{v_1138}) & S=union(S1_1346,{v_1343}) & 
  APP(S_1191,S1_1147,S2_1150) & S2_1150=S2 & S1_1346=S_1191 & 
  v_1138=v_1343 & S1_1141=S1_1147 & S_1191=))))) --> APP(S,S1,S2),
 (S=S2 & S1=) --> APP(S,S1,S2),
 (exists(S1_1252:exists(v_1249:exists(S1_1282:exists(v_1279:exists(S1_1269:exists(v_1266:exists(S1_1141:exists(v_1138:S1_1252=S1_1282 & 
  v_1249=v_1279 & S_1191=union(S1_1252,{v_1249}) & S_1191!=() & 
  S1_1269=union(S1_1282,{v_1279}) & S1_1141=S1_1147 & v_1138=v_1266 & 
  S2_1150=S2 & APP(S_1191,S1_1147,S2_1150) & S=union(S1_1269,{v_1266}) & 
  S1=union(S1_1141,{v_1138}) & S1!=()))))))))) --> APP(S,S1,S2),
 (exists(S1_1346:exists(v_1343:exists(S1_1141:exists(v_1138:S_1191= & 
  S1_1141=S1_1147 & v_1138=v_1343 & S1_1346=S_1191 & S2_1150=S2 & 
  APP(S_1191,S1_1147,S2_1150) & S=union(S1_1346,{v_1343}) & S1=union(S1_1141,
  {v_1138}) & S1!=()))))) --> APP(S,S1,S2)]
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
                              EXISTS(flted_54_1660,Anon_1661,
                              S_1662: res::dll<Anon_1661,flted_54_1660,S_1662>@M[Orig][LHSCase]@ rem br[{286,285}]&
                              (
                              ([S_1662=union(S1,S2)]
                               [flted_54_1660=m+n & 0<=m & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S=S2 & S1=) --> C(S,S1,S2),
 (exists(S1_1538:exists(v_1535:exists(S1_1572:exists(v_1569:exists(S1_1559:exists(v_1556:exists(S1_1428:exists(v_1425:S1_1538=S1_1572 & 
  v_1535=v_1569 & S_1485=union(S1_1538,{v_1535}) & S_1485!=() & 
  S1_1559=union(S1_1572,{v_1569}) & S1_1428=S1_1434 & v_1425=v_1556 & 
  S2_1437=S2 & C(S_1485,S1_1434,S2_1437) & S=union(S1_1559,{v_1556}) & 
  S1!=() & S1=union(S1_1428,{v_1425})))))))))) --> C(S,S1,S2),
 (exists(S1_1636:exists(v_1633:exists(S1_1428:exists(v_1425:S_1477= & 
  S1_1636= & S1_1434=S1_1428 & v_1425=v_1633 & S2=S2_1437 & 
  C(S_1477,S1_1434,S2_1437) & S=union(S1_1636,{v_1633}) & S1!=() & 
  S1=union(S1_1428,{v_1425})))))) --> C(S,S1,S2)]
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

Total verification time: 14.92 second(s)
	Time spent in main process: 1.45 second(s)
	Time spent in child processes: 13.47 second(s)


Processing file "bst_msh.ss"
Parsing bst_msh.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure append$node2~node2... 
Procedure append$node2~node2 SUCCESS

Checking procedure appendC$node2~node2... 
Procedure appendC$node2~node2 SUCCESS

Checking procedure count$node2... 
!!! REL :  CNT(h,h1)
!!! POST:  h1>=0 & h1=h
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [CNT]
              EBase exists (Expl)(Impl)[n; 
                    h](ex)z::bst1<n,h>@M[Orig][LHSCase]@ rem br[{287,286}]&(
                    ([0<=n][0<=h]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 15::
                                EXISTS(n_90,
                                h1: z::bst1<n_90,h1>@M[Orig][LHSCase]@ rem br[{287,286}]&
                                (
                                ([0<=h1 & CNT(h,h1)]
                                 [n=n_90 & n=res & 0<=n_90]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  h](ex)z::bst1<n,h>@M[Orig][LHSCase]@ rem br[{287,286}]&(
                  ([0<=n][0<=h]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 15::
                              EXISTS(n_1303,
                              h1_1304: z::bst1<n_1303,h1_1304>@M[Orig][LHSCase]@ rem br[{287,286}]&
                              (
                              ([h=h1_1304 & 0<=h][res=n & res=n_1303 & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (h1=0 & h=0) --> CNT(h,h1),
 (h=0 & h1=0) --> CNT(h,h1),
 (CNT(h_1237,h1_1251) & CNT(h_1255,h1_1272) & (h=h_1237+1 & h1=h1_1251+1 & 
  0<=h_1255 & h_1255<=h_1237 & 0<=h1_1272 & h1_1272<=h1_1251 | h=h_1255+1 & 
  h1=h1_1272+1 & 0<=h1_1251 & h1_1251<h1_1272 & 0<=h_1237 & h_1237<h_1255 | 
  h=h_1237+1 & h1=h1_1272+1 & 0<=h_1255 & h_1255<=h_1237 & 0<=h1_1251 & 
  h1_1251<h1_1272 | h=h_1255+1 & h1=h1_1251+1 & 0<=h_1237 & h_1237<h_1255 & 
  0<=h1_1272 & h1_1272<=h1_1251)) --> CNT(h,h1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure count$node2 SUCCESS

Checking procedure remove_min$node2... 
Procedure remove_min$node2 SUCCESS

Checking procedure delete$node2~int... 
assert:bst_msh.ss:192: 16:  : ok


!!! REL :  DEL(h,h1)
!!! POST:  0=h1 & 0=h | h1>=1 & h>=h1
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [DEL]
              EBase exists (Expl)(Impl)[n; 
                    h](ex)x::bst1<n,h>@M[Orig][LHSCase]@ rem br[{287,286}]&(
                    ([0<=n][0<=h]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 39::ref [x]
                                EXISTS(n1,
                                h1: x'::bst1<n1,h1>@M[Orig][LHSCase]@ rem br[{287,286}]&
                                (([0<=h1 & DEL(h,h1)][0<=n1]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  h](ex)x::bst1<n,h>@M[Orig][LHSCase]@ rem br[{287,286}]&(
                  ([0<=n][0<=h]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 39::ref [x]
                              EXISTS(n1_1671,
                              h1_1672: x'::bst1<n1_1671,h1_1672>@M[Orig][LHSCase]@ rem br[{287,286}]&
                              (
                              ([0<=n1_1671]
                               [(0=h1_1672 & 0=h | h1_1672>=1 & 
                                 h>=h1_1672) & 0<=h1_1672 & 0<=h]
                               [0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (-1+h=h1 & 1<=h1) --> DEL(h,h1),
 (exists(n1_1440:exists(n2_1562:1+h1=h & 1+n1_1440=h & 0<=n2_1562 & (2+
  n2_1562)<=h) | 1+h1=h & 1+n1_1440=h & exists(n1_1559:0<=n1_1559 & (3+
  n1_1559)<=h))) --> DEL(h,h1),
 (false) --> DEL(h,h1),
 (exists(h_1456:h1=h & 1<=h_1456 & (1+h_1456)<=h & 
  exists(h1_1604:h1_1604<=h_1456 & 0<=h1_1604) | exists(n1_1440:-1+
  h=h_1456 & (2+n1_1440)<=h1 & (-1+h1)<=h_1456 & 0<=n1_1440) | 
  exists(h1_1604:0<=h1_1604 & (1+h1_1604)<=h1) & -1+h=h_1456 & 
  h1<=h_1456)) --> DEL(h,h1),
 (DEL(h_1482,h1_1626) & (h=h1 & 0<=h_1482 & h_1482<h1 & 0<=h1_1626 & 
  h1_1626<h1 | h1=h1_1626+1 & h=h_1482+1 & 1<=h1_1626 & 1<=h_1482 | 
  h1=h1_1626+1 & 0<=h_1482 & h_1482<h & h<=h1_1626 | h=h_1482+1 & 
  0<=h1_1626 & h1_1626<h1 & h1<=h_1482)) --> DEL(h,h1),
 (exists(n2_1443:DEL(h_1494,h1_1649) & (1+h_1494=h & 1+h1_1649=h1 & 
  0<=n2_1443 & (1+n2_1443)<=h1 & (1+n2_1443)<=h | h1=h & 1+n2_1443=h & 
  0<=h1_1649 & (2+h1_1649)<=h & 0<=h_1494 & (2+h_1494)<=h | 1+h_1494=h & 1+
  n2_1443=h1 & (2+h1_1649)<=h1 & h1<=h & 0<=h1_1649 | 1+n2_1443=h & 1+
  h1_1649=h1 & (2+h_1494)<=h & h<=h1 & 0<=h_1494))) --> DEL(h,h1),
 (h1=0 & h=0) --> DEL(h,h1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete$node2~int SUCCESS

Checking procedure flatten$node2... 
Procedure flatten$node2 SUCCESS

Checking procedure insert$node2~int... 
Procedure insert$node2~int SUCCESS

Checking procedure search$node2~int... 
!!! REL :  SEA(h,h1)
!!! POST:  h>=0 & h=h1
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [SEA]
              EBase exists (Expl)(Impl)[n; 
                    h](ex)x::bst1<n,h>@M[Orig][LHSCase]@ rem br[{287,286}]&(
                    ([0<=n][0<=h]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 50::
                                EXISTS(n_64,
                                h1: x::bst1<n_64,h1>@M[Orig][LHSCase]@ rem br[{287,286}]&
                                (
                                ([res | !(res)][0<=h1 & SEA(h,h1)]
                                 [n=n_64 & 0<=n_64]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  h](ex)x::bst1<n,h>@M[Orig][LHSCase]@ rem br[{287,286}]&(
                  ([0<=n][0<=h]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 50::
                              EXISTS(n_2207,
                              h1_2208: x::bst1<n_2207,h1_2208>@M[Orig][LHSCase]@ rem br[{287,286}]&
                              (
                              ([h=h1_2208 & 0<=h][n=n_2207 & 0<=n]
                               [res | !(res)]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (h1=0 & h=0) --> SEA(h,h1),
 (exists(n2_2090:h1=h & 0<=n2_2090 & (1+n2_2090)<=h | exists(n1_2087:h1=h & 
  1+n2_2090=h & 0<=n1_2087 & (2+n1_2087)<=h))) --> SEA(h,h1),
 (SEA(h_2105,h1_2161) & (h=h1 & 0<=h_2105 & h_2105<h1 & 0<=h1_2161 & 
  h1_2161<h1 | h1=h1_2161+1 & h=h_2105+1 & 1<=h1_2161 & 1<=h_2105 | 
  h1=h1_2161+1 & 0<=h_2105 & h_2105<h & h<=h1_2161 | h=h_2105+1 & 
  0<=h1_2161 & h1_2161<h1 & h1<=h_2105)) --> SEA(h,h1),
 (exists(n2_2090:SEA(h_2118,h1_2182) & (1+h_2118=h & 1+h1_2182=h1 & 
  0<=n2_2090 & (1+n2_2090)<=h1 & (1+n2_2090)<=h | h1=h & 1+n2_2090=h & 
  0<=h1_2182 & (2+h1_2182)<=h & 0<=h_2118 & (2+h_2118)<=h | 1+h_2118=h & 1+
  n2_2090=h1 & (2+h1_2182)<=h1 & h1<=h & 0<=h1_2182 | 1+n2_2090=h & 1+
  h1_2182=h1 & (2+h_2118)<=h & h<=h1 & 0<=h_2118))) --> SEA(h,h1),
 (h=0 & h1=0) --> SEA(h,h1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure search$node2~int SUCCESS

Checking procedure traverse$node2... 
!!! REL :  TRAV(h,h1)
!!! POST:  h1>=0 & h1=h
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [TRAV]
              EBase exists (Expl)(Impl)[n; 
                    h](ex)x::bst1<n,h>@M[Orig][LHSCase]@ rem br[{287,286}]&(
                    ([0<=n][0<=h]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 48::
                                EXISTS(n_69,
                                h1: x::bst1<n_69,h1>@M[Orig][LHSCase]@ rem br[{287,286}]&
                                (([0<=h1 & TRAV(h,h1)][n=n_69 & 0<=n_69]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  h](ex)x::bst1<n,h>@M[Orig][LHSCase]@ rem br[{287,286}]&(
                  ([0<=n][0<=h]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 48::
                              EXISTS(n_2292,
                              h1_2293: x::bst1<n_2292,h1_2293>@M[Orig][LHSCase]@ rem br[{287,286}]&
                              (([h=h1_2293 & 0<=h][n=n_2292 & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (h1=0 & h=0) --> TRAV(h,h1),
 (TRAV(h_2247,h1_2260) & TRAV(h_2256,h1_2267) & (h=h_2247+1 & h1=h1_2260+1 & 
  0<=h_2256 & h_2256<=h_2247 & 0<=h1_2267 & h1_2267<=h1_2260 | h=h_2256+1 & 
  h1=h1_2267+1 & 0<=h1_2260 & h1_2260<h1_2267 & 0<=h_2247 & h_2247<h_2256 | 
  h=h_2247+1 & h1=h1_2267+1 & 0<=h_2256 & h_2256<=h_2247 & 0<=h1_2260 & 
  h1_2260<h1_2267 | h=h_2256+1 & h1=h1_2260+1 & 0<=h_2247 & h_2247<h_2256 & 
  0<=h1_2267 & h1_2267<=h1_2260)) --> TRAV(h,h1),
 (h=0 & h1=0) --> TRAV(h,h1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure traverse$node2 SUCCESS

Termination checking result:

Stop Omega... 1508 invocations 
0 false contexts at: ()

Total verification time: 1.15 second(s)
	Time spent in main process: 0.43 second(s)
	Time spent in child processes: 0.72 second(s)
